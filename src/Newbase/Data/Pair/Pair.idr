---------------------
-- Module declaration
---------------------

module Newbase.Data.Pair.Pair

-----------------
-- Pair data type
-----------------

public export
data Pair : Type -> Type -> Type where
  MkPair : (x : a) -> (y : b) -> Pair a b

public export
fst : Pair a b -> a
fst (MkPair x y) = x

public export
snd : Pair a b -> b
snd (MkPair x y) = y

%pair Pair fst snd

----------------
-- Triplet alias
----------------

public export
Triplet : Type -> Type -> Type -> Type
Triplet a b c = Pair a (Pair b c)

public export
mkTriplet : (x : a) -> (y : b) -> (z : c) -> Triplet a b c
mkTriplet x y z = MkPair x (MkPair y z)

public export
tripFst : Triplet a b c -> a
tripFst trip = fst trip

public export
tripSnd : Triplet a b c -> b
tripSnd trip = fst (snd trip)

public export
tripTrd : Triplet a b c -> c
tripTrd trip = snd (snd trip)
