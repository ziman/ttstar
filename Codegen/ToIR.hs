module Codegen.ToIR (toIR) where

import TT.Core
import TT.Utils (unApplyPat)
import TT.Pretty ()

import Codegen.IR

import Data.Ord
import Data.List
import Data.Function

toIR :: TT () -> IR
toIR = irTm 0

irName :: Name -> IName
irName n = IMN (show n) 0

irTm :: Int -> TT () -> IR
irTm pv (V n) = IV (irName n)
irTm pv (App () f x) = IApp (irTm pv f) (irTm pv x)
irTm pv (Bind Lam [Def n () _ty _body _cs] rhs) = ILam (irName n) (irTm pv rhs)
irTm pv (Bind Let [] rhs) = irTm pv rhs
irTm pv (Bind Let (Def n () ty body _cs : ds) rhs)
    = ILet (irName n) (irBody pv ty body) $ irTm pv (Bind Let ds rhs)
irTm pv tm = error $ "irTm: cannot translate: " ++ show tm

irBody :: Int -> TT () -> Body () -> IBody
irBody pv ty (Clauses cs) = ICaseTree $ compile pv cs
irBody pv ty (Term tm) = ICaseTree $ ILeaf (irTm pv tm)
irBody pv ty (Abstract Constructor) = IConstructor (length $ argNames ty)
irBody pv ty (Abstract Postulate) = ICaseTree $ ILeaf (IError "postulate")
irBody pv ty (Abstract (Foreign code)) = IForeign code
irBody pv ty b = error $ "irBody: cannot translate: " ++ show b

argNames :: TT () -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

compile :: Int -> [Clause ()] -> ICaseTree
compile pv clauses
    = matchSort pvars pats $ ILeaf (IError "unreachable case")
  where
    pv' = pv + width
    pvars = [pv + i | i <- [0..width-1]]
    widths = map (length . fst) pats
    width = if maximum widths == minimum widths then minimum widths else error "compile: pat width mismatch"
    pats = [(map snd . snd $ unApplyPat lhs, irTm pv' rhs) | Clause pvs lhs rhs <- clauses]

matchSort :: [Int] -> [([Pat ()], IR)] -> ICaseTree -> ICaseTree
matchSort vars pats err = match vars pats err

match :: [Int] -> [([Pat ()], IR)] -> ICaseTree -> ICaseTree
match [] [([], rhs)] err = ILeaf rhs
match vars pats err
    | isVar firstPat
    = let (pats', rest) = span (isVar . head . fst) pats
        in ruleVar vars pats' $ match vars rest err

    | isCtor firstPat
    = let (pats', rest) = span (isCtor . head . fst) pats
        in ruleCtor vars pats' $ match vars rest err

    | otherwise
    = error $ "match: unsupported pattern: " ++ show firstPat
  where
    firstPat = head . fst . head $ pats

    isVar (PV n) = True
    isVar _ = False

    isCtor pat@(PApp r f x) | (PV cn, args) <- unApplyPat pat = True
    isCtor _ = False

ruleVar :: [Int] -> [([Pat ()], IR)] -> ICaseTree -> ICaseTree
ruleVar (v:vs) pats err = matchSort vs pats' err
  where
    pats' = [(ps, substIR (irName n) v rhs) | (PV n : ps, rhs) <- pats]

ruleCtor :: [Int] -> [([Pat ()], IR)] -> ICaseTree -> ICaseTree
ruleCtor (v:vs) pats err = ICase v $ alts ++ [IDefault err]
  where
    getCtor (p : ps, rhs) | (PV cn, args) <- unApplyPat p = cn
    sorted = sortBy (comparing fst) [(irName $ getCtor p, p) | p <- pats]
    grouped = groupBy ((==) `on` fst) sorted
    alts = map (mkAlt vs) grouped

mkAlt :: [Int] -> [(IName, ([Pat ()], IR))] -> IAlt
mkAlt vs grp

-- we know that the substituted name is unique
substIR :: IName -> Int -> IR -> IR
substIR n v (IV n') | n == n' = IV $ IPV v
substIR n v iv@(IV n') = iv
substIR n v (ILam n' rhs) = ILam n' (substIR n v rhs) 
substIR n v (ILet n' b rhs) = ILet n' (substIRB n v b) (substIR n v rhs)
substIR n v (IApp f x) = IApp (substIR n v f) (substIR n v x)
substIR n v ir@(IError s) = ir

substIRB :: IName -> Int -> IBody -> IBody
substIRB n v (ICaseTree ct) = ICaseTree $ substIRCT n v ct
substIRB n v b = b

substIRCT :: IName -> Int -> ICaseTree -> ICaseTree
substIRCT n v (ILeaf tm) = ILeaf $ substIR n v tm
substIRCT n v (ICase v' alts)
    = ICase v' (map (substIRA n v) alts)

substIRA :: IName -> Int -> IAlt -> IAlt
substIRA n v (ICtor cn pvs rhs) = ICtor cn pvs $ substIRCT n v rhs
substIRA n v (IDefault rhs) = IDefault $ substIRCT n v rhs
