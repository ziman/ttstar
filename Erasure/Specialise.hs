module Erasure.Specialise (specialise) where

import TT
import TTLens

import Erasure.Meta
import Erasure.Check
import Erasure.Solve

import Control.Arrow
import Control.Applicative
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State
import Data.Traversable
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

import Lens.Family2

newtype Instances = Instances (M.Map Name (S.Set ErPattern))
type ErPattern = [Relevance]
type Spec = Writer Instances

instance Monoid Instances where
    mempty = Instances M.empty
    mappend (Instances p) (Instances q)
        = Instances $ M.unionWith S.union p q

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

extend ::
    Program Meta
    -> Instances
    -> Program Meta
    -> Program Meta
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

remetaify :: Program Relevance -> Program Meta
remetaify = progRelevance %~ Fixed

specialise ::
    Program Meta          -- raw, just metaified definitions (material to specialise)   
    -> Program Relevance  -- program to extend
    -> Program Meta       -- extended program
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

specNAlt :: Alt Relevance -> Spec (Alt Relevance)
specNAlt (Alt lhs rhs) = Alt <$> specNLHS lhs <*> specNTm rhs

specNLHS :: AltLHS Relevance -> Spec (AltLHS Relevance)
specNLHS Wildcard = pure Wildcard
specNLHS (Ctor cn args eqs) = Ctor cn <$> traverse specNDef args <*> traverse specEq eqs
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

specNTm (Bind b d tm) = Bind b <$> specNDef d <*> specNTm tm
specNTm (App r f x) = App r <$> specNTm f <*> specNTm x
specNTm (Case r s ty alts) = Case r <$> specNTm s <*> specNTm ty <*> traverse specNAlt alts

specName :: Name -> ErPattern -> Name
specName (UN n) epat = IN n epat
specName n _ = error $ "trying to specialise a strange name: " ++ show n
