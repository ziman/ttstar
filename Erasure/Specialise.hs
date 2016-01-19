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

specialise :: Program Relevance VoidConstrs -> Program Relevance VoidConstrs
specialise (Prog defs) = Prog $ map specNDef defs

specNDef :: Def Relevance VoidConstrs -> Def Relevance VoidConstrs
specNDef (Def n r ty mtm Nothing)
    = Def n r (specNTm ty) (specNTm <$> mtm) Nothing

specNTm :: TT Relevance -> TT Relevance
specNTm (V n) = V n
specNTm (I n ty) = V (specName n ty)
specNTm (Bind b n r ty tm) = Bind b n r (specNTm ty) (specNTm tm)
specNTm (App r f x) = App r (specNTm f) (specNTm x)
specNTm (Let def tm) = Let (specNDef def) (specNTm tm)
specNTm (Case s alts) = Case (specNTm s) (map specNAlt alts)
specNTm  Type = Type
specNTm  Erased = Erased

specNAlt :: Alt Relevance -> Alt Relevance
specNAlt (ConCase n tm) = ConCase n $ specNTm tm
specNAlt (DefaultCase tm) = DefaultCase $ specNTm tm

specName :: Name -> TT Relevance -> Name
specName (UN n) ty = IN n (ty ^.. ttRelevance)

specName' :: Name -> ErPattern -> Name
specName' (UN n) epat = IN n epat
