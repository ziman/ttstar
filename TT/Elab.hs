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
    deriving (Show)

newtype Backtrace = BT [String]
data Constr = Eq Term Term
data ElabFailure = ElabFailure Backtrace ElabErr

type Elab a = RWST
    (Ctx MRel)            -- R: context
    (S.Set Constr)        -- W: constraints
    ElabState             -- S: for fresh names
    (Except ElabFailure)  -- T: errors
    a

elabTm :: Term -> Elab ()
elabTm _tm = undefined

-- solve all metas
elab :: Term -> Term
elab tm = tm
