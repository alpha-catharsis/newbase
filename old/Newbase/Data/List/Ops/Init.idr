---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Init

----------
-- imports
----------

import Newbase.Data.List.Rels.Proper

------------
-- list init
------------

public export
init : (xs : List a) -> (0 prf : Proper xs) -> List a
init [x]          _ = []
init (x::x'::xs') _ = x::init (x'::xs') IsProper
