---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.Has

----------------------
-- List has k elements
----------------------

public export
data Has : (0 k : Nat) -> (0 e : a) -> (0 xs : List a) -> Type where
  HasNone : Has 0 e []
  HasNext : Has k e xs -> Has (S k) e (e::xs)
  MissNext : Has k e xs -> Not (e = e') -> Has k e (e'::xs)
