module Erasure where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict

import TTstar

data Meta = MVar Int | Fixed Relevance deriving (Eq, Ord, Show)
type TTmeta = TT' Meta
type MetaM = State Int

meta :: Program TT -> Program TTmeta
meta prog = evalState (metaProg prog) 0

metaProg :: Program TT -> MetaM (Program TTmeta)
metaProg = mapM metaDef

metaDef :: Def TT -> MetaM (Def TTmeta)
metaDef (Fun n ty tm) = Fun n <$> metaTm ty <*> metaTm tm

fresh :: State Int Meta
fresh = modify (+1) >> MVar <$> get

fresh' :: Maybe Relevance -> State Int Meta
fresh' Nothing  = fresh
fresh' (Just r) = return $ Fixed r

metaTm :: TT -> MetaM TTmeta
metaTm (V n) = return $ V n
metaTm (Bind bnd r n ty tm) = Bind bnd <$> fresh' r <*> pure n <*> metaTm ty <*> metaTm tm
metaTm (App r f x) = App <$> fresh' r <*> metaTm f <*> metaTm x
metaTm (Prim op args) = Prim op <$> mapM metaTm args
metaTm (C c) = return $ C c
