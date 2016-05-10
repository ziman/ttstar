module Erasure.Prune where

import TT
import Pretty
import Control.Applicative
import qualified Data.Set as S

prune :: Program Relevance VoidConstrs -> Program () VoidConstrs
prune (Prog defs) = Prog $ pruneDefs eds defs
  where
    -- elided defs
    eds = S.fromList [n | Def n E _ _ _ <- defs]

pruneDef :: S.Set Name -> Def Relevance VoidConstrs -> [Def () VoidConstrs]
pruneDef eds (Def n E ty body mcs) = []
pruneDef eds (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody eds body) Nothing]

pruneBody :: S.Set Name -> Body Relevance -> Body ()
pruneBody eds (Abstract a)  = Abstract a
pruneBody eds (Term tm)     = Term $ pruneTm eds tm
pruneBody eds (Patterns cf) = Patterns $ pruneCaseFun eds cf

pruneCaseFun :: S.Set Name -> CaseFun Relevance -> CaseFun ()
pruneCaseFun eds (CaseFun args ct)
    = CaseFun (pruneDefs eds args) (pruneCaseTree eds ct)

pruneCaseTree :: S.Set Name -> CaseTree Relevance -> CaseTree ()
pruneCaseTree eds (Leaf tm) = Leaf $ pruneTm eds tm
pruneCaseTree eds (Case E s [Alt lhs rhs]) = pruneCaseTree eds rhs
pruneCaseTree eds (Case R s alts) = Case () (pruneTm eds s) $ map (pruneAlt eds) alts

pruneAlt :: S.Set Name -> Alt Relevance -> Alt ()
pruneAlt eds (Alt lhs rhs) = Alt (pruneAltLHS eds lhs) (pruneCaseTree eds rhs)

pruneAltLHS :: S.Set Name -> AltLHS Relevance -> AltLHS ()
pruneAltLHS eds Wildcard = Wildcard
pruneAltLHS eds (Ctor cn args eqs)
    = Ctor cn (pruneDefs eds args) [(n, pruneTm eds tm) | (n, tm) <- eqs]

pruneDefs :: S.Set Name -> [Def Relevance VoidConstrs] -> [Def () VoidConstrs]
pruneDefs eds = concatMap (pruneDef eds)

pruneTm :: S.Set Name -> TT Relevance -> TT ()
pruneTm eds (V n) = V n
pruneTm eds (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm eds (Bind b d tm)
    = case pruneDef eds d of
        []   -> pruneTm (S.insert (defName d) eds) tm  -- remember the elided definition
        [d'] -> Bind b d' (pruneTm eds tm)
pruneTm eds (App E f x) = pruneTm eds f
pruneTm eds (App R f x) = App () (pruneTm eds f) (pruneTm eds x)
