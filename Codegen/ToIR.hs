module Codegen.ToIR (toIR) where

import TT.Core
import TT.Utils (unApplyPat, subst)
import TT.Pretty ()

import Codegen.IR

import Data.Ord
import Data.List
import Data.Function

import Debug.Trace
import Codegen.Pretty

toIR :: TT () -> IR
toIR = irTm 0

irName :: Name -> IName
irName n = IUN (show n)

irTm :: Int -> TT () -> IR
irTm pv (V n) = IV (irName n)
irTm pv (App () f x) = IApp (irTm pv f) (irTm pv x)
irTm pv (Bind Lam [Def n () _ty _body _cs] rhs) = ILam (irName n) (irTm pv rhs)
irTm pv (Bind Let [] rhs) = irTm pv rhs
irTm pv (Bind Let (Def n () ty body _cs : ds) rhs)
    = ILet (irName n) (irBody pv ty body) $ irTm pv (Bind Let ds rhs)
irTm pv tm = error $ "irTm: cannot translate: " ++ show tm

irBody :: Int -> TT () -> Body () -> IBody
irBody pv ty (Clauses cs) = compile pv cs
irBody pv ty (Term tm) = ICaseFun [] $ ILeaf (irTm pv tm)
irBody pv ty (Abstract Constructor) = IConstructor (length $ argNames ty)
irBody pv ty (Abstract Postulate) = ICaseFun [] $ ILeaf (IError "postulate")
irBody pv ty (Abstract (Foreign code)) = IForeign code
irBody pv ty b = error $ "irBody: cannot translate: " ++ show b

argNames :: TT () -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

compile :: Int -> [Clause ()] -> IBody
compile pv clauses
    = ICaseFun pvars $ matchSort pv' pvars pats (ILeaf $ IError "unreachable case")
  where
    pv' = pv + width
    pvars = [pv + i | i <- [0..width-1]]
    widths = map (length . fst) pats
    width = if maximum widths == minimum widths then minimum widths else error "compile: pat width mismatch"
    pats = [(map snd . snd $ unApplyPat lhs, rhs) | Clause pvs lhs rhs <- clauses]

matchSort :: Int -> [Int] -> [([Pat ()], TT ())] -> ICaseTree -> ICaseTree
matchSort pv vars pats err = match pv vars pats err

match :: Int -> [Int] -> [([Pat ()], TT ())] -> ICaseTree -> ICaseTree
match pv vars [] err = err
match pv [] [(ps, rhs)] err = ILeaf $ irTm pv rhs
match pv [] ((ps, rhs):_) err = ILeaf $ irTm pv rhs  -- overlapping patterns
match pv vars pats err
    | isVar firstPat
    = let (pats', rest) = span (isVar . head . fst) pats
        in ruleVar pv vars pats' $ match pv vars rest err

    | isCtor firstPat
    = let (pats', rest) = span (isCtor . head . fst) pats
        in ruleCtor pv vars pats' $ match pv vars rest err

    | otherwise
    = error $ "match: unsupported pattern: " ++ show firstPat
  where
    firstPat = head . fst . head $ pats

    isVar (PV n) = True
    isVar _ = False

    isCtor pat@(PApp r f x) | (PV cn, args) <- unApplyPat pat = True
    isCtor _ = False

ruleVar :: Int -> [Int] -> [([Pat ()], TT ())] -> ICaseTree -> ICaseTree
ruleVar pv [] pats err = error $ "ruleVar: empty vars"
ruleVar pv (v:vs) pats err = matchSort pv vs pats' err
  where
    pats' = [(ps, subst n (V $ MN "pv" v) rhs) | (PV n : ps, rhs) <- pats]

ruleCtor :: Int -> [Int] -> [([Pat ()], TT ())] -> ICaseTree -> ICaseTree
ruleCtor pv [] pats err = error $ "ruleCtor: empty vars"
ruleCtor pv (v:vs) pats err = ICase v $ alts ++ [IDefault err]
  where
    getCtor (p : ps, rhs) | (PV cn, args) <- unApplyPat p = cn
    getCtor tm = error $ "getCtor: " ++ show tm

    sorted = sortBy (comparing fst) [(irName $ getCtor p, p) | p <- pats]
    grouped = groupBy ((==) `on` fst) sorted
    alts = map (\grp -> mkAlt pv vs grp err) grouped

mkAlt :: Int -> [Int] -> [(IName, ([Pat ()], TT ()))] -> ICaseTree -> IAlt
mkAlt pv vs grp err
    = ICtor cn pvs $ matchSort pv' vs' pats' err
  where
    pats' = [((map snd . snd $ unApplyPat p) ++ ps, rhs) | (cn, (p:ps, rhs)) <- grp]
    vs' = pvs ++ vs
    pv' = pv + arity
    pvs = [pv + i | i <- [0..arity-1]]
    cn = fst . head $ grp
    arity = length . snd . unApplyPat . head . fst . snd . head $ grp
