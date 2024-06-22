---------------------
-- Module declaration
---------------------

module Newbase.Data.Fin.Fin

----------
-- imports
----------

import Newbase.Data.Nat.Rels.LT

----------------
-- Fin data type
----------------

public export
data Fin : (0 k : Nat) -> Type where
  MkFin : (m : Nat) -> (0 prf : LT m k) -> Fin k
