module Erasure.InstGlob (instantiateGlobals) where

import TT
import Pretty
import Util.PrettyPrint

import qualified Data.Set as S
import Control.Applicative
import Control.Monad.Trans.State.Strict

type InstM = State Int

instantiateGlobals :: Program r cs -> Program r cs
instantiateGlobals prog@(Prog defs) = evalState (instProg globals prog) 0
  where
    globals = S.fromList [n | Def n _ _ _ _ <- defs]

instProg :: S.Set Name -> Program r cs -> InstM (Program r cs)
instProg glob (Prog defs) = Prog <$> mapM (instDef glob) defs

instDef :: S.Set Name -> Def r cs -> InstM (Def r cs)
instDef glob (Def n r ty Nothing mcs)
    = Def n r <$> instTm glob ty <*> pure Nothing <*> pure mcs
instDef glob (Def n r ty (Just tm) mcs)
    = Def n r <$> instTm glob ty <*> (Just <$> instTm glob tm) <*> pure mcs

instTm :: S.Set Name -> TT r -> InstM (TT r)
instTm glob (V n)
    | n `S.member` glob = I n <$> fresh
    | otherwise         = return $ V n
instTm glob (I n i) = return $ I n i
instTm glob (Bind b n r ty tm) = Bind b n r <$> instTm glob ty <*> instTm glob tm
instTm glob (App r f x) = App r <$> instTm glob f <*> instTm glob x
instTm glob (Let def tm)
    = Let <$> instDef glob def <*> instTm glob tm
instTm glob (Case s alts) = Case <$> instTm glob s <*> mapM (instAlt glob) alts
instTm glob Type = return Type
instTm glob Erased = return Erased

instAlt :: S.Set Name -> Alt r -> InstM (Alt r)
instAlt glob (ConCase n rhs) = ConCase n <$> instTm glob rhs
instAlt glob (DefaultCase rhs) = DefaultCase <$> instTm glob rhs

fresh :: InstM Int
fresh = modify (+1) >> get
