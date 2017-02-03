module Erasure.Specialise (specialise) where

import TT
import TTLens

import Erasure.Meta
import Erasure.Check

import Control.Monad.Trans.State
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

import Lens.Family2

type Instances = M.Map Name (S.Set ErPattern)
type ErPattern = [Relevance]
type Spec a = State Int (Instances, a)

fresh :: State Int Int
fresh = do
    i <- get
    put $ i+1
    return i

bindMetas :: [Relevance] -> [Meta] -> IM.IntMap Meta
bindMetas [] [] = IM.empty
bindMetas (r : rs) (m : ms) = bind r m $ bindMetas rs ms
  where
    bind R (Fixed R) = id
    bind E (Fixed E) = id
    bind r (MVar  i) = IM.insert i (Fixed r)
    bind r m = error $ "bindMetas.bind: inconsistency: " ++ show (r, m)
bindMetas rs ms = error $ "bindMetas: length mismatch: " ++ show (rs, ms)

specName :: Name -> ErPattern -> Name
specName (UN n) epat = IN n epat
specName n _ = error $ "trying to specialise a strange name: " ++ show n

specialise ::
    Program Meta          -- raw, just metaified definitions (material to specialise)   
    -> Program Relevance  -- program to extend
    -> Program Meta       -- extended program
specialise pm pr
    | M.null residue = pr'
    | otherwise = error $ "could not specialise: " ++ show residue
  where
    (residue, pr') = evalState (specTm pm pr) initialState

    initialState :: Int
    initialState = 1 + maximum (0 : [
        i | MVar i <- pm ^.. (ttRelevance :: Traversal' (TT Meta) Meta)
      ])

forMany :: (f Meta -> f Relevance -> Spec (f Meta)) -> [f Meta] -> [f Relevance] -> Spec [f Meta]
forMany spec ms rs = do
    xs <- sequence [spec m r | (m, r) <- zip ms rs]
    return (
        M.unionsWith S.union $ map fst xs,
        map snd xs
      )

specCT :: CtorTag Meta -> CtorTag Relevance -> CtorTag Meta
specCT (CT nm rm) (CT nr rr) = CT nr $ Fixed rr
specCT (CTForced nm) (CTForced nr) = CTForced nr
specCT ctm ctr = error $ "specCT: mismatch: " ++ show (ctm, ctr)

specAlt :: Alt Meta -> Alt Relevance -> Spec (Alt Meta)
specAlt (Alt Wildcard rhsm) (Alt Wildcard rhsr)
    = fmap (Alt Wildcard) <$> specCaseTree rhsm rhsr
specAlt (Alt (Ctor ctm dsm) rhsm) (Alt (Ctor ctr dsr) rhsr) = do
    (isRhs, rhsr') <- specCaseTree rhsm rhsr
    (isDefs, dsr') <- forMany specDef dsm dsr
    return (
        M.unionWith S.union isRhs isDefs,
        Alt (Ctor (specCT ctm ctr) dsr') rhsr'
      )
specAlt (Alt (ForcedVal ftmm) rhsm) (Alt (ForcedVal ftmr) rhsr) = do
    (isFtm, ftmr') <- specTm ftmm ftmr
    (isRhs, rhsr') <- specCaseTree rhsm rhsr
    return (
        M.unionWith S.union isRhs isFtm,
        Alt (ForcedVal ftmr') rhsr'
      )
specAlt altm altr = error $ "specAlt: mismatch: " ++ show (altm, altr)

specCaseTree :: CaseTree Meta -> CaseTree Relevance -> Spec (CaseTree Meta)
specCaseTree (Leaf tmm) (Leaf tmr) = fmap Leaf <$> specTm tmm tmr
specCaseTree (Case rm sm altsm) (Case rr sr altsr) = do
    (is, sr') <- specTm sm sr
    (is', altsr') <- forMany specAlt altsm altsr
    return (
        M.unionWith S.union is is',
        Case (Fixed rr) sr' altsr'
      )
specCaseTree ctm ctr = error $ "specCaseTree: mismatch: " ++ show (ctm, ctr)

specCaseFun :: CaseFun Meta -> CaseFun Relevance -> Spec (CaseFun Meta)
specCaseFun (CaseFun dsm ctm) (CaseFun dsr ctr) = do
    -- spec the definitions first
    (is, dsr') <- forMany specDef dsm dsr
    (is', ctr') <- specCaseTree ctm ctr
    return (
        M.unionWith S.union is is',
        CaseFun dsr' ctr'
      )

specBody :: Body Meta -> Body Relevance -> Spec (Body Meta)
specBody bm (Abstract a) = return $ (M.empty, Abstract a)
specBody (Term tmm) (Term tmr) = fmap Term <$> specTm tmm tmr
specBody (Patterns cfm) (Patterns cfr) = fmap Patterns <$> specCaseFun cfm cfr
specBody bm br = error $ "specBody: non-matching bodies: " ++ show (bm, br)

specDef :: Def Meta -> Def Relevance -> Spec (Def Meta)
specDef (Def nm rm tym bodym _csm) (Def nr rr tyr bodyr csr) = do
    (is, tyr') <- specTm tym tyr
    (is', bodyr') <- specBody bodym bodyr
    return $ (M.unionWith S.union is is', Def nr (Fixed rr) tyr' bodyr' noConstrs)

specTm :: TT Meta -> TT Relevance -> Spec (TT Meta)
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
        instantiate fresh (bindMetas ep (defType dm ^.. (ttRelevance :: Traversal' (TT Meta) Meta)))
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

specTm (Forced tmm) (Forced tmr) = fmap Forced <$> specTm tmm tmr

specTm tmm tmr = error $ "cannot specialise: " ++ show (tmm, tmr)
