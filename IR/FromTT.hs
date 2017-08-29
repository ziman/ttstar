module IR.FromTT (toIR) where

import TT.Core
import TT.Utils (unApplyPat, subst)
import TT.Pretty ()

import IR.Core
import IR.Prune

import Data.Ord
import Data.List
import Data.Function

import qualified Data.Set as S

{-
import Debug.Trace
import IR.Pretty ()
-}

toIR :: TT () -> IR
toIR = pruneIR . irTm S.empty 0

irName :: Name -> IName
irName Blank = IBlank
irName (MN "pv" i) = IPV i
irName n = IUN (show n)

irTm :: S.Set Name -> Int -> TT () -> IR
irTm cs pv (V n) = IV (irName n)
irTm cs pv (App () f x) = IApp (irTm cs pv f) (irTm cs pv x)
irTm cs pv (Bind Lam [Def n () _ty _body _cs] rhs) = ILam (irName n) (irTm cs pv rhs)
irTm cs pv (Bind Let [] rhs) = irTm cs pv rhs
irTm cs pv (Bind Let (Def n () ty body _cs : ds) rhs)
    = ILet (irName n) (irBody cs pv ty body) $ irTm cs' pv (Bind Let ds rhs)
  where
    cs' | Abstract Constructor <- body = S.insert n cs
        | otherwise = cs

irTm cs pv tm = IError $ "irTm: cannot translate: " ++ show tm

irBody :: S.Set Name -> Int -> TT () -> Body () -> IBody
irBody cs pv ty (Clauses cls) = compile cs pv cls
irBody cs pv ty (Term tm) = ICaseFun [] $ ILeaf (irTm cs pv tm)
irBody cs pv ty (Abstract Constructor) = IConstructor (length $ argNames ty)
irBody cs pv ty (Abstract (Foreign code)) = IForeign code
irBody cs pv ty (Abstract Postulate) = IConstructor (length $ argNames ty)
    -- ^^ compiling like constructors is practical for unerased programs
irBody cs pv ty b = error $ "irBody: cannot translate: " ++ show b

argNames :: TT () -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

compile :: S.Set Name -> Int -> [Clause ()] -> IBody
compile cs pv clauses
    = ICaseFun pvars $ matchSort cs pv' pvars pats Nothing
  where
    pv' = pv + width
    pvars = [pv + i | i <- [0..width-1]]
    widths = map (length . fst) pats
    width | maximum widths == minimum widths = minimum widths
          | otherwise = error "compile: pat width mismatch"
    pats = [(map snd . snd $ unApplyPat lhs, rhs) | Clause pvs lhs rhs <- clauses]

matchSort :: S.Set Name -> Int -> [Int] -> [([Pat ()], TT ())] -> Maybe ICaseTree -> ICaseTree
matchSort cs pv vars pats err = match cs pv vars pats err

match :: S.Set Name -> Int -> [Int] -> [([Pat ()], TT ())] -> Maybe ICaseTree -> ICaseTree
--match cs pv vars pats err | ("MATCH", vars, pats, err) `traceShow` False = undefined
match cs pv vars [] Nothing = {-ILeaf $ IError "pattern match failure" -} error $ "match: no fallback tree: " ++ show (cs, pv, vars)
match cs pv vars [] (Just err) = err
match cs pv [] [(ps, rhs)] err = ILeaf $ irTm cs pv rhs
match cs pv [] ((ps, rhs):_) err = ILeaf $ irTm cs pv rhs  -- overlapping patterns
match cs pv vars pats err
    | isVar firstPat
    = let (pats', rest) = span (isVar . head . fst) pats
        in ruleVar cs pv vars pats' $ case rest of
                                        [] -> err
                                        _  -> Just (match cs pv vars rest err)

    | isCtor firstPat
    = let (pats', rest) = span (isCtor . head . fst) pats
        in ruleCtor cs pv vars pats' $ case rest of
                                        [] -> err
                                        _  -> Just (match cs pv vars rest err)

    | otherwise
    = error $ "match: unsupported pattern: " ++ show firstPat
  where
    firstPat = head . fst . head $ pats

    isVar (PForced _) = True
    isVar (PV n) = S.notMember n cs
    isVar _ = False

    isCtor (PV n) = S.member n cs
    isCtor pat@(PApp r f x) | (PV cn, args) <- unApplyPat pat = True
    isCtor pat@(PApp r f x) | (PForced _, args) <- unApplyPat pat = True
    isCtor _ = False

ruleVar :: S.Set Name -> Int -> [Int] -> [([Pat ()], TT ())] -> Maybe ICaseTree -> ICaseTree
--ruleVar cs pv vs pats err | ("VAR", vs, pats, err) `traceShow` False = undefined
ruleVar cs pv [] pats err = error $ "ruleVar: empty vars"
ruleVar cs pv (v:vs) pats err = matchSort cs pv vs (map substPat pats) err
  where
    substPat (PV n : ps, rhs) = (ps, subst n (V $ MN "pv" v) rhs)
    substPat (PForced _ : ps, rhs) = (ps, rhs)
    substPat (p:ps, rhs) = error $ "substPat: unsupported pattern: " ++ show p
    substPat ([], rhs) = error $ "substPat: no patterns for: " ++ show rhs

ruleCtor :: S.Set Name -> Int -> [Int] -> [([Pat ()], TT ())] -> Maybe ICaseTree -> ICaseTree
--ruleCtor cs pv vs pats err | ("CTOR", vs, pats, err) `traceShow` False = undefined
ruleCtor cs pv [] pats err = error $ "ruleCtor: empty vars"
ruleCtor cs pv (v:vs) pats err = ICase v alts'
  where
    getCtor (p : ps, rhs) | (PV cn, args) <- unApplyPat p = cn
    getCtor (p : ps, rhs) | (PForced _, args) <- unApplyPat p = Blank
    getCtor tm = error $ "getCtor: " ++ show tm

    sorted = sortBy (comparing fst) [(irName $ getCtor p, p) | p <- pats]
    grouped = groupBy ((==) `on` fst) sorted
    alts = map (\grp -> mkAlt cs pv vs grp err) grouped
    alts' | Just e <- err = alts ++ [IDefault e]
          | otherwise     = alts

mkAlt :: S.Set Name -> Int -> [Int] -> [(IName, ([Pat ()], TT ()))] -> Maybe ICaseTree -> IAlt
mkAlt cs pv vs grp err
    = ICtor cn pvs $ matchSort cs pv' vs' pats' err
  where
    pats' = [((map snd . snd $ unApplyPat p) ++ ps, rhs) | (cn, (p:ps, rhs)) <- grp]
    vs' = pvs ++ vs
    pv' = pv + arity
    pvs = [pv + i | i <- [0..arity-1]]
    cn = fst . head $ grp
    arity = length . snd . unApplyPat . head . fst . snd . head $ grp
