---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Tail

----------
-- imports
----------

import Newbase.Data.List.Rels.Proper

------------
-- list tail
------------

public export
tail : (xs : List a) -> (0 prf : Proper xs) -> List a
tail (x::xs') _ = xs'
