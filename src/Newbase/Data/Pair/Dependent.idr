---------------------
-- Module declaration
---------------------

module Newbase.Data.Pair.Dependent

---------------------------
-- Dependent pair data type
---------------------------

public export
data DPair : (a : Type) -> (a -> Type) -> Type where
  MkDPair : (x : a) -> (y : p x) -> DPair a p

public export
fst : DPair a p -> a
fst (MkDPair x y) = x

public export
snd : (pr : DPair a p) -> p (fst pr)
snd (MkDPair x y) = y
