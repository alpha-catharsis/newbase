---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.Prefix

--------------
-- List prefix
--------------

public export
data Prefix : List a -> List a -> Type where
  NilPrefix : Prefix [] xs
  ConsPrefix : Prefix xs ys -> Prefix (z::xs) (z::ys)
