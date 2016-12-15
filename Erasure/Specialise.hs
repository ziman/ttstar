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

{-
extend ::
    Defs Meta
    -> Instances
    -> Defs Meta
    -> Defs Meta
extend (Prog rawDefs) (Instances imap) prog@(Prog defs)
    = Prog $ evalState (concat <$> traverse expandDef defs) initialState
  where
    initialState = 1 + maximum (0 : [i | MVar i <- prog ^.. (progRelevance :: Traversal' (Program Meta) Meta)])
    rawDefMap = M.fromList [(n, d) | d@(Def n r ty _ _) <- rawDefs]

    extendDefs oldName
      = sequence
          [ let Def _ r ty body noCs = rawDefMap M.! oldName
                newName = specName oldName ep
              in instantiate fresh (bindMetas ep (ty ^.. (ttRelevance :: Traversal' (TT Meta) Meta)))
                   $ Def newName r ty body noCs
          | ep <- S.toList $ M.findWithDefault S.empty oldName imap
          ]

    expandDef (Def n r ty body noCs) = (Def n r ty body noCs :) <$> extendDefs n
-}

specName :: Name -> ErPattern -> Name
specName (UN n) epat = IN n epat
specName n _ = error $ "trying to specialise a strange name: " ++ show n

specialise ::
    Program Meta          -- raw, just metaified definitions (material to specialise)   
    -> Program Relevance  -- program to extend
    -> Program Meta       -- extended program
specialise (Prog dsm) (Prog dsr)
    | M.null residue = Prog dsr'
    | otherwise = error $ "could not specialise: " ++ show residue
  where
    (residue, Bind Let dsr' _main) = evalState core initialState
    core = specTm (Bind Let dsm (V Blank)) (Bind Let dsr (V Blank))

    initialState :: Int
    initialState = 1 + maximum (0 : [
        i | d <- dsm
          , MVar i <- d ^.. (defRelevance :: Traversal' (Def Meta) Meta)
      ])

specTm :: TT Meta -> TT Relevance -> Spec (TT Meta)
specTm tmm (V n) = return (M.empty, V n)
specTm tmm (I n@(UN ns) ty)
    = return (spec n rs, V (IN ns rs))
  where
    rs :: [Relevance]
    rs = ty ^.. (ttRelevance ::Traversal' (TT Relevance) Relevance)

    spec :: Name -> [Relevance] -> Instances
    spec n = M.singleton n . S.singleton

specTm (Bind bm [] tmm) (Bind br [] tmr) = do
    (is, tmr') <- specTm tmm tmr
    return (is, Bind br [] tmr')

specTm (Bind bm (dm:dsm) tmm) (Bind br (dr:dsr) tmr) = do
    (is, Bind _br' dsr' tmr') <- specTm (Bind bm dsm tmm) (Bind br dsr tmr)
    specs <- sequence [
        instantiate fresh (bindMetas ep (defType dm ^.. (ttRelevance :: Traversal' (TT Meta) Meta)))
            $ dm{ defName = specName n ep }
        | ep <- S.toList $ M.findWithDefault S.empty n is
      ]
    return (
        M.delete n is,
        Bind br (specs ++ dsr') tmr'
      )
  where
    n = defName dr

specTm (App rm fm xm) (App rr fr xr) = do
    (isf, fr') <- specTm fm fr
    (isx, xr') <- specTm xm xr
    return (M.unionWith S.union isf isx, App (Fixed rr) fr' xr')

specTm (Forced tmm) (Forced tmr) = do
    (is, tmr') <- specTm tmm tmr
    return (is, Forced tmr')

specTm tmm tmr = error $ "cannot specialise: " ++ show (tmm, tmr)

{-
specialise raw prog = extend raw insts $ remetaify prog'
  where
    (prog', insts) = runWriter $ specNProg prog

specNProg :: Program Relevance -> Spec (Program Relevance)
specNProg (Prog defs) = Prog <$> traverse specNDef defs

specNDef :: Def Relevance -> Spec (Def Relevance)
specNDef (Def n r ty body noCs)
    = Def n r <$> specNTm ty <*> specNBody body <*> pure noCs

specNBody :: Body Relevance -> Spec (Body Relevance)
specNBody (Abstract a)  = pure $ Abstract a
specNBody (Term tm)     = Term <$> specNTm tm
specNBody (Patterns cf) = Patterns <$> specNCaseFun cf

specNCaseFun :: CaseFun Relevance -> Spec (CaseFun Relevance)
specNCaseFun (CaseFun args ct) = CaseFun <$> traverse specNDef args <*> specNCaseTree ct

specNCaseTree :: CaseTree Relevance -> Spec (CaseTree Relevance)
specNCaseTree (Leaf tm) = Leaf <$> specNTm tm
specNCaseTree (Case r s alts) = Case r <$> specNTm s <*> traverse specNAlt alts

specNAlt :: Alt Relevance -> Spec (Alt Relevance)
specNAlt (Alt lhs rhs) = Alt <$> specNLHS lhs <*> specNCaseTree rhs

specNLHS :: AltLHS Relevance -> Spec (AltLHS Relevance)
specNLHS Wildcard = pure Wildcard
specNLHS (Ctor r cn args eqs) = Ctor r cn <$> traverse specNDef args <*> traverse specEq eqs
  where
    specEq (n, tm) = (,) n <$> specNTm tm

specNTm :: TT Relevance -> Spec (TT Relevance)
specNTm (V n) = pure $ V n

specNTm (I n@(UN ns) ty) = do
    let rs = ty ^.. (ttRelevance :: Traversal' (TT Relevance) Relevance)
    tell $ spec n rs
    return $ V (IN ns rs)
  where
    spec :: Name -> [Relevance] -> Instances
    spec n = Instances . M.singleton n . S.singleton

specNTm (Bind b ds tm) = Bind b <$> traverse specNDef ds <*> specNTm tm
specNTm (App r f x) = App r <$> specNTm f <*> specNTm x

specNTm tm = error $ "unexpected term to specialise: " ++ show tm
-}
