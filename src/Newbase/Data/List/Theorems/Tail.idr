---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Tail

----------
-- imports
----------

import Newbase.Data.List.Ops.Head
import Newbase.Data.List.Ops.Tail
import Newbase.Data.List.Rels.Elem
import Newbase.Data.List.Rels.Proper

------------
-- Tail cons
------------

public export
tailCons : tail (x::xs) IsProper = xs
tailCons = Refl

public export
headTailCons : {0 xs : List a} -> (prf : Proper xs) -> 
               head xs prf ::tail xs prf = xs
headTailCons IsProper = Refl
