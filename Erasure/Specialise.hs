module Erasure.Specialise (specialise) where

import TT
import TTLens

import Erasure.Evar
import Erasure.Infer

import Control.Monad.Trans.State
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

import Lens.Family2

type Instances = M.Map Name (S.Set ErPattern)
type ErPattern = [Relevance]
type Spec a = State Int (Instances, a)

-- The Spec monad works as follows:
-- 1. we specialise the given term, returning it as the "a" in (Instances, a)
-- 2. on the side, we also gather all instances methioned within, and return
--    them as the "Instances" in (Instances, a)
-- 3. this knowledge of which instances are mentioned in subterms
--    is necessary to instantiate let-bindings.
-- 4. the whole thing happens in the state monad
-- 5. we pass the raw metaified term because we need material for let-definitions;
--    everywhere else we just recurse in parallel without interaction

fresh :: State Int Int
fresh = do
    i <- get
    put $ i+1
    return i

bindEvars :: [Relevance] -> [Evar] -> IM.IntMap Evar
bindEvars [] [] = IM.empty
bindEvars (r : rs) (m : ms) = bind r m $ bindEvars rs ms
  where
    bind R (Fixed R) = id
    bind E (Fixed E) = id
    bind r (EV  i) = IM.insert i (Fixed r)
    bind r m = error $ "bindEvars.bind: inconsistency: " ++ show (r, m)
bindEvars rs ms = error $ "bindEvars: length mismatch: " ++ show (rs, ms)

specName :: Name -> ErPattern -> Name
specName (UN n) epat = IN n epat
specName n _ = error $ "trying to specialise a strange name: " ++ show n

specialise ::
    Program Evar          -- raw, just evarified definitions (material to specialise)   
    -> Program Relevance  -- program to extend
    -> Program Evar       -- extended program
specialise pm pr
    | M.null residue = pr'
    | otherwise = error $ "could not specialise: " ++ show residue
  where
    (residue, pr') = evalState (specTm pm pr) initialState

    initialState :: Int
    initialState = 1 + maximum (0 : [
        i | EV i <- pm ^.. (ttRelevance :: Traversal' (TT Evar) Evar)
      ])

specClause :: Clause Evar -> Clause Relevance -> Spec (Clause Evar)
specClause (Clause pm lm rm) (Clause pr lr rr) = do
    isp' <- sequence [specDef m r | (m,r) <- zip pm pr]
    let isp = M.unionsWith S.union $ map fst isp'
    let p' = map snd isp'
    (isl, l') <- specPat lm lr
    (isr, r') <- specTm rm rr
    return (M.unionsWith S.union [isp,isl,isr], Clause p' l' r')

specBody :: Body Evar -> Body Relevance -> Spec (Body Evar)
specBody bm (Abstract a) = return $ (M.empty, Abstract a)
specBody (Term tmm) (Term tmr) = fmap Term <$> specTm tmm tmr
specBody (Clauses csm) (Clauses csr) = do
    tss <- sequence [specClause m r | (m, r) <- zip csm csr]
    return (M.unionsWith S.union $ map fst tss, Clauses $ map snd tss)
specBody bm br = error $ "specBody: non-matching bodies: " ++ show (bm, br)

specDef :: Def Evar -> Def Relevance -> Spec (Def Evar)
specDef (Def nm rm tym bodym _csm) (Def nr rr tyr bodyr csr) = do
    (is, tyr') <- specTm tym tyr
    (is', bodyr') <- specBody bodym bodyr
    return $ (M.unionWith S.union is is', Def nr (Fixed rr) tyr' bodyr' noConstrs)

specPat :: Pat Evar -> Pat Relevance -> Spec (Pat Evar)
specPat pm (PV n) = return (M.empty, PV n)
specPat (PApp rm fm xm) (PApp rr fr xr) = do
    (isf, fr') <- specPat fm fr
    (isx, xr') <- specPat xm xr
    return (M.unionWith S.union isf isx, PApp (Fixed rr) fr' xr')
specPat (PForced tm) (PForced tr) = fmap PForced <$> specTm tm tr

specPat pm pr = error $ "cannot specialise: " ++ show (pm, pr)

specTm :: TT Evar -> TT Relevance -> Spec (TT Evar)
specTm tmm (V n) = return (M.empty, V n)
specTm tmm (I n@(UN ns) ty)
    = return (spec n rs, V (IN ns rs))
  where
    rs :: [Relevance]
    rs = ty ^.. (ttRelevance ::Traversal' (TT Relevance) Relevance)

    spec :: Name -> [Relevance] -> Instances
    spec n = M.singleton n . S.singleton

specTm (Bind bm [] tmm) (Bind br [] tmr) = fmap (Bind br []) <$> specTm tmm tmr

specTm (Bind bm (dm:dsm) tmm) (Bind br (dr:dsr) tmr) = do
    (isDef, dr') <- specDef dm dr
    (isSub, Bind _br' dsr' tmr') <- specTm (Bind bm dsm tmm) (Bind br dsr tmr)
    let is = M.unionWith S.union isDef isSub
    specs <- sequence [
        instantiate fresh (bindEvars ep (defType dm ^.. (ttRelevance :: Traversal' (TT Evar) Evar)))
            $ dm{ defName = specName n ep }
        | ep <- S.toList $ M.findWithDefault S.empty n is
      ]
    return (
        M.delete n is,
        Bind br (dr' : specs ++ dsr') tmr'
      )
  where
    n = defName dr

specTm (App rm fm xm) (App rr fr xr) = do
    (isf, fr') <- specTm fm fr
    (isx, xr') <- specTm xm xr
    return (M.unionWith S.union isf isx, App (Fixed rr) fr' xr')

specTm tmm tmr = error $ "cannot specialise: " ++ show (tmm, tmr)
