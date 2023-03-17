---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.Proper

--------------
-- Proper list
--------------

public export
data Proper : List a -> Type where
  IsProper : Proper (x::xs)
