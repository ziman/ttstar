module TTSExp where

import SExp
import TT
import Erasure.Evar

import qualified Data.Map as M
import qualified Data.Set as S

class SexpR r where
    sexpR :: r -> SExp
    unsexpR :: SExp -> Either String r

instance SexpR () where
    sexpR () = SV "_"

    unsexpR (SV "_") = Right ()
    unsexpR s = Left $ "not relevance: " ++ show s

instance SexpR Relevance where
    sexpR R = SV "R"
    sexpR E = SV "E"

    unsexpR (SV "R") = Right R
    unsexpR (SV "E") = Right E
    unsexpR s = Left $ "not relevance: " ++ show s

instance SexprR (Maybe Relevance) where
    sexpR Nothing = SV "_"
    sexpR (Just r) = sexpR r

    unsexpR (SV "_") = Right $ Nothing
    unsexpR r = Just <$> unsexpR r

instance SexpR Evar where
    sexpR (Fixed r) = sexpR r
    sexpR (EV i) = SI i
    
    unsexpR (SI i) = Right $ EV i
    unsexpR r = Fixed <$> unsexpR r

sexpTT :: SexpR r => TT r -> SExp
sexpTT (V n) = SL [SV "V", SV n]
sexpTT (I n ty) = SL [SV "I", SV n, sexpTT ty]
sexpTT (Bind b d tm) = SL [SV "B", sexpB b, sexpDef d, sexpTT tm]
sexpTT (App r f x) = SL [SV "A", sexpR r, sexpTT f, sexpTT x]

sexpB :: Binder -> SExp
sexpB Lam = SV "lam"
sexpB Pi  = SV "pi"
sexpB Let = SV "let"

sexpDef :: SexpR r => Def r -> SExp
sexpDef (Def n r ty b cs) = SL [
    SV n, sexpR r, sexpTT ty, sexpBody b, sexpCs cs
  ]

sexpBody :: SexpR r => Body r -> SExp
sexpBody (Abstract Var) = SV "var"
sexpBody (Abstract Postulate) = SV "postulate"
sexpBody (Abstract (Foreign code)) = SL [SV "foreign", SV code]
sexpBody (Term tm) = SL [SV "term", sexpTT tm]
sexpBody (Clauses cs) = SL (SV "clauses" : map sexpClause cs)

sexpCs :: SexpR r => Constrs r -> SExp
sexpCs cs = SL [SL [sexpRs g, sexpRs c] | (g,c) <- M.toList cs]

sexpRs :: SexpR r => S.Set r -> SExp
sexpRs rs = SL (map sexpR . S.toList $ rs)

sexpClause :: SexpR r => Clause r -> SExp
sexpClause (Clause pvs lhs rhs)
    = SL [SL (map sexpDef pvs), sexpTm lhs, sexpTm rhs]
