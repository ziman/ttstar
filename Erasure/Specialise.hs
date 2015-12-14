module Erasure.Specialise (specialise) where

import TT
import TTLens

import Control.Arrow
import Control.Applicative
import Control.Traversable
import Control.Monad.Trans.State
import qualified Data.Map as M
import qualified Data.Set as S

type ErPattern = [Relevance]
type PatMap = M.Map Name (S.Set ErPattern)

specialise :: Program Relevance VoidConstrs -> Program Relevance VoidConstrs
specialise prog = Prog $ concatMap (specialiseDef pmap) defs'
  where
    (Prog defs', pmap) = specNames prog

-- specialise names and also find out which specialisations we need for every name
specNames :: Program Relevance VoidConstrs -> (Program Relevance VoidConstrs, M.Map Name (S.Set ErPattern))
specNames prog = runStateT (specNProg prog) M.empty

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
    let erPattern = ty ^.. ttRelevance
    announce n erPattern
    return $ specName n erPattern
specNTm (Bind b n r ty tm) = Bind b n r <$> specNTm ty <*> specNTm tm

specName :: Name -> ErPattern -> Name
specName n epat = n ++ "_" ++ concatMap show epat

announce :: Name -> ErPattern -> State PatMap ()
announce n epat = modify $ M.insertWith S.union n (S.singleton epat)

specialiseDef :: PatMap -> Def Relevance VoidConstrs -> [Def Relevance VoidConstrs]
specialiseDef pmap d = [d]
