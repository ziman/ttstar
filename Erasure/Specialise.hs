module Erasure.Specialise (specialise) where

import TT
import TTLens

import Erasure.Meta

import Control.Arrow
import Control.Applicative
import Control.Monad.Trans.Writer
import Data.Traversable
import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Family

newtype Instances = Instances (M.Map Name (S.Set ErPattern))
type ErPattern = [Relevance]
type Spec = Writer Instances

instance Monoid Instances where
    mempty = Instances M.empty
    mappend (Instances p) (Instances q)
        = Instances $ M.unionWith S.union p q

extend ::
    Program Meta VoidConstrs
    -> Instances
    -> Program Meta VoidConstrs
    -> Program Meta VoidConstrs
extend (Prog rawDefs) (Instances imap) (Prog defs)
    = Prog $ concatMap expandDef defs
  where
    rawDefMap = M.fromList [(n, d) | d@(Def n r ty _ _) <- rawDefs]
    extendDefs n
      = [ let 
            Def _ r ty mtm Nothing = rawDefMap M.! n
            in Def (specName n ep) r ty mtm Nothing
        | ep <- S.toList $ M.findWithDefault S.empty n imap
        ]
    expandDef d@(Def n r ty mtm Nothing) = d : extendDefs n

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
specNDef (Def n r ty mtm Nothing)
    = Def n r <$> specNTm ty <*> traverse specNTm mtm <*> pure Nothing

specNTm :: TT Relevance -> Spec (TT Relevance)
specNTm (V n) = pure $ V n

specNTm (I n@(UN ns) ty) = do
    let rs = ty ^.. ttRelevance
    tell $ spec n rs
    return $ V (IN ns rs)
  where
    spec :: Name -> [Relevance] -> Instances
    spec n = Instances . M.singleton n . S.singleton

specNTm (Bind b n r ty tm) = Bind b n r <$> specNTm ty <*> specNTm tm
specNTm (App r f x) = App r <$> specNTm f <*> specNTm x
specNTm (Let def tm) = Let <$> specNDef def <*> specNTm tm
specNTm (Case s alts) = Case <$> specNTm s <*> traverse specNAlt alts
specNTm  Type = pure Type
specNTm  Erased = pure Erased

specNAlt :: Alt Relevance -> Spec (Alt Relevance)
specNAlt (ConCase n tm) = ConCase n <$> specNTm tm
specNAlt (DefaultCase tm) = DefaultCase <$> specNTm tm

specName :: Name -> ErPattern -> Name
specName (UN n) epat = IN n epat
