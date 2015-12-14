module Erasure.Specialise (specialise) where

import TT
import TTLens

import Control.Arrow
import Control.Applicative
import Control.Monad.Trans.State
import Data.Traversable
import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Family

type ErPattern = [Relevance]
type PatMap = M.Map Name (S.Set ErPattern)

specialise :: Program Relevance VoidConstrs -> Program Relevance VoidConstrs
specialise prog = Prog $ concatMap (specialiseDef pmap) defs'
  where
    (Prog defs', pmap) = specNames prog

-- specialise names and also find out which specialisations we need for every name
specNames :: Program Relevance VoidConstrs -> (Program Relevance VoidConstrs, PatMap)
specNames prog = runState (specNProg prog) M.empty

specNProg :: Program Relevance VoidConstrs -> State PatMap (Program Relevance VoidConstrs)
specNProg (Prog defs) = Prog <$> traverse specNDef defs

specNDef :: Def Relevance VoidConstrs -> State PatMap (Def Relevance VoidConstrs)
specNDef (Def n r ty mtm Nothing)
    = Def n r
        <$> specNTm ty
        <*> traverse specNTm mtm
        <*> pure Nothing

specNTm :: TT Relevance -> State PatMap (TT Relevance)
specNTm (V n) = return $ V n
specNTm (I n ty) = do
    ty' <- specNTm ty
    let erPattern = ty' ^.. ttRelevance
    announce n erPattern
    return $ V (specName n erPattern)

specNTm (Bind b n r ty tm) = Bind b n r <$> specNTm ty <*> specNTm tm
specNTm (App r f x) = App r <$> specNTm f <*> specNTm x
specNTm (Let def tm) = Let <$> specNDef def <*> specNTm tm
specNTm (Case s alts) = Case <$> specNTm s <*> traverse specNAlt alts
specNTm  Type = return Type
specNTm  Erased = return Erased

specNAlt :: Alt Relevance -> State PatMap (Alt Relevance)
specNAlt (ConCase n tm) = ConCase n <$> specNTm tm
specNAlt (DefaultCase tm) = DefaultCase <$> specNTm tm

specName :: Name -> ErPattern -> Name
specName n epat = n ++ "_" ++ concatMap show epat

announce :: Name -> ErPattern -> State PatMap ()
announce n epat = modify $ M.insertWith S.union n (S.singleton epat)

specialiseDef :: PatMap -> Def Relevance VoidConstrs -> [Def Relevance VoidConstrs]
specialiseDef pmap d = [d]
