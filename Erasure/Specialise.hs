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

import Lens.Family

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
    Program Meta VoidConstrs
    -> Instances
    -> Program Meta VoidConstrs
    -> Program Meta VoidConstrs
extend (Prog rawDefs) (Instances imap) prog@(Prog defs)
    = Prog $ evalState (concat <$> traverse expandDef defs) initialState
  where
    initialState = 1 + maximum (0 : [i | MVar i <- prog ^.. progRelevance])
    rawDefMap = M.fromList [(n, d) | d@(Def n r ty _ _) <- rawDefs]

    extendDefs oldName
      = sequence
          [ let Def _ r ty body Nothing = rawDefMap M.! oldName
                newName = specName oldName ep
              in instantiate fresh (bindMetas ep (ty ^.. ttRelevance))
                   $ Def newName r ty (specLHS newName body) Nothing
          | ep <- S.toList $ M.findWithDefault S.empty oldName imap
          ]

    expandDef (Def n r ty mtm Nothing) = (Def n r ty mtm Nothing :) <$> extendDefs n

specLHS :: Name -> Body r -> Body r
specLHS n (Clauses cls) = Clauses $ map (specLHS' n) cls
specLHS n body = body

specLHS' :: Name -> Clause r -> Clause r
specLHS' n (Clause pvs lhs rhs) = Clause pvs lhs' rhs
  where
    (V _oldN, args) = unApply lhs
    lhs' = mkApp (V n) args

remetaify :: Program Relevance VoidConstrs -> Program Meta VoidConstrs
remetaify = progRelevance %~ Fixed

specialise ::
    Program Meta VoidConstrs          -- raw, just metaified definitions (material to specialise)   
    -> Program Relevance VoidConstrs  -- program to extend
    -> Program Meta VoidConstrs       -- extended program
specialise raw prog = extend raw insts $ remetaify prog'
  where
    (prog', insts) = runWriter $ specNProg prog

specNProg :: Program Relevance VoidConstrs -> Spec (Program Relevance VoidConstrs)
specNProg (Prog defs) = Prog <$> traverse specNDef defs

specNDef :: Def Relevance VoidConstrs -> Spec (Def Relevance VoidConstrs)
specNDef (Def n r ty body Nothing)
    = Def n r <$> specNTm ty <*> specNBody body <*> pure Nothing

specNBody :: Body Relevance -> Spec (Body Relevance)
specNBody (Abstract a)  = pure $ Abstract a
specNBody (Term tm)     = Term <$> specNTm tm
specNBody (Clauses cls) = Clauses <$> traverse specNClause cls

specNClause :: Clause Relevance -> Spec (Clause Relevance)
specNClause (Clause pvs lhs rhs)
    = Clause <$> traverse specNDef pvs <*> specNTm lhs <*> specNTm rhs

specNTm :: TT Relevance -> Spec (TT Relevance)
specNTm (V n) = pure $ V n

specNTm (I n@(UN ns) ty) = do
    let rs = ty ^.. ttRelevance
    tell $ spec n rs
    return $ V (IN ns rs)
  where
    spec :: Name -> [Relevance] -> Instances
    spec n = Instances . M.singleton n . S.singleton

specNTm (Bind b d tm) = Bind b <$> specNDef d <*> specNTm tm
specNTm (App r f x) = App r <$> specNTm f <*> specNTm x
specNTm (Forced tm) = Forced <$> specNTm tm

specName :: Name -> ErPattern -> Name
specName (UN n) epat = IN n epat
specName n _ = error $ "trying to specialise a strange name: " ++ show n
