---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.Elem

---------------------------
-- List element proposition
---------------------------

public export
data Elem : a -> List a -> Type where
  Here : Elem x (x::xs)
  There : Elem x xs -> Elem x (y::xs)
