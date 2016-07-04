module Erasure.Prune where

import TT
import Pretty
import Control.Applicative
import qualified Data.Set as S

prune :: Program Relevance -> Program ()
prune (Prog defs) = Prog $ pruneDefs defs

pruneDef :: Def Relevance -> [Def ()]
pruneDef (Def n E ty body mcs) = []
pruneDef (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody body) noConstrs]

pruneBody :: Body Relevance -> Body ()
pruneBody (Abstract a)  = Abstract a
pruneBody (Term tm)     = Term $ pruneTm tm

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (Alt lhs rhs) = Alt (pruneAltLHS lhs) (pruneTm rhs)

pruneAltLHS :: AltLHS Relevance -> AltLHS ()
pruneAltLHS Wildcard = Wildcard
pruneAltLHS (Ctor cn args eqs)
    = Ctor cn (pruneDefs args) []  -- just remove all eqs

pruneDefs :: [Def Relevance] -> [Def ()]
pruneDefs = concatMap pruneDef

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind b d tm)
    = case pruneDef d of
        []   -> pruneTm tm
        [d'] -> Bind b d' (pruneTm tm)
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Case E s ty [Alt lhs rhs]) = pruneTm rhs
pruneTm (Case R s ty alts) = Case () (pruneTm s) (V Blank) $ map pruneAlt alts
pruneTm t@(Case E s ty alts) = error $ "trying to prune non-singleton tree: " ++ show t
