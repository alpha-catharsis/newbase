---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Head

----------
-- imports
----------

import Newbase.Data.List.Rels.Proper

------------
-- list head
------------

public export
head : (xs : List a) -> (0 prf : Proper xs) -> a
head (x::xs') _ = x
