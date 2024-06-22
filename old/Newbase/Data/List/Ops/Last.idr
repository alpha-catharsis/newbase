---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Last

----------
-- imports
----------

import Newbase.Data.List.Rels.Proper

------------
-- list last
------------

public export
last : (xs : List a) -> (0 prf : Proper xs) -> a
last [x]        _ = x
last (_::x::xs) _ = last (x::xs) IsProper
