module TT.Elab (elab) where

import TT.Core
import TT.Pretty

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State (evalStateT, StateT)
import Control.Monad.Trans.RWS.Strict
import qualified Control.Monad.Trans.State as State

import qualified Data.Set as S
import qualified Data.Map as M

type MRel = Maybe Relevance
type Term = TT MRel
type Type = TT MRel

type ElabState = ()
data ElabErr
    = CantUnify Term Term
    | CantElaborate Term
    deriving (Show)

newtype Backtrace = BT [String]
data Constr = Eq Term Term deriving (Eq, Ord, Show)

data ElabFailure = ElabFailure Backtrace ElabErr
instance Show ElabFailure where
    show (ElabFailure (BT []) e) = show e
    show (ElabFailure (BT bt) e) = unlines $
            "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1::Integer ..]
                (reverse bt)
            ++ ["Error: " ++ show e]


type Elab a = RWST
    (Ctx MRel, Backtrace) -- R: context
    (S.Set Constr)        -- W: constraints
    ElabState             -- S: for fresh names
    (Except ElabFailure)  -- T: errors
    a

efail :: ElabErr -> Elab a
efail err = do
    (_, bt) <- ask
    lift . throwE $ ElabFailure bt err

elabTm :: Term -> Elab Type
elabTm tm = efail $ CantElaborate tm

-- solve all metas
elab :: Term -> Either String Term
elab tm =
    case runExcept $ evalRWST (elabTm tm) (M.empty, BT []) () of
        Left err -> Left $ show err
        Right (_ty, cs) -> error $ show cs
