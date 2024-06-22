---------------------
-- Module declaration
---------------------

module Newbase.Data.Nat.Nat

------------------
-- Natural numbers
------------------

public export
data Nat : Type where
  Z : Nat
  S : Nat -> Nat
