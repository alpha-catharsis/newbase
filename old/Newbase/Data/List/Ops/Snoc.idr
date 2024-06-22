---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Snoc

------------
-- List snoc
------------

public export
snoc : (x : a) -> (xs : List a) -> List a
snoc x xs = xs ++ [x]
