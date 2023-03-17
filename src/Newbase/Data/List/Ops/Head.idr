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
head : (xs : List a) -> {auto 0 pprf : Proper xs} -> a
head []       impossible
head (x::xs') = x
