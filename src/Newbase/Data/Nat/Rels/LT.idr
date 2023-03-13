---------------------
-- Module declaration
---------------------

module Newbase.Data.Nat.Rels.LT

--------------------------
-- Nat lower than relation
--------------------------

public export
data LT : (0 m : Nat) -> (0 n : Nat) -> Type where
  LTZero : LT Z (S n)
  LTSucc : LT m n -> LT (S m) (S n)
