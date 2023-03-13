---------------------
-- Module declaration
---------------------

module Newbase.Data.Nat.Rels.LTE

--------------------------------------
-- Nat lower than or equal to relation
--------------------------------------

public export
data LTE : (0 m : Nat) -> (0 n : Nat) -> Type where
  LTEZero : LTE Z n
  LTESucc : LTE m n -> LTE (S m) (S n)
