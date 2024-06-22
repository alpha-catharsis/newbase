---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.Postfix

----------
-- Imports
----------

import Newbase.Data.List.Ops.Snoc

---------------
-- List postfix
---------------

public export
data Postfix : List a -> List a -> Type where
  NilPostfix : Postfix [] xs
  SnocPostfix : Postfix xs ys -> Postfix (snoc z xs) (snoc z ys)
