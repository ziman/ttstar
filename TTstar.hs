-- | Terms in the core language. The type parameter is the type of
-- identifiers used for bindings and explicit named references;
-- usually we use @TT 'Name'@.
data TT n = P NameType n (TT n) -- ^ named references with type
            -- (P for "Parameter", motivated by McKinna and Pollack's
            -- Pure Type Systems Formalized)
          | V !Int -- ^ a resolved de Bruijn-indexed variable
          | Bind n !(Binder (TT n)) (TT n) -- ^ a binding
          | App (AppStatus n) !(TT n) (TT n) -- ^ function, function type, arg
          | Constant Const -- ^ constant
          | Proj (TT n) !Int -- ^ argument projection; runtime only
                             -- (-1) is a special case for 'subtract one from BI'
          | Erased -- ^ an erased term
          | Impossible -- ^ special case for totality checking
          | TType UExp -- ^ the type of types at some level
          | UType Universe -- ^ Uniqueness type universe (disjoint from TType)
  deriving (Ord, Functor, Data, Typeable)
{-!
deriving instance Binary TT
deriving instance NFData TT
