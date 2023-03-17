---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Head

----------
-- imports
----------

import Newbase.Data.List.Ops.Head
import Newbase.Data.List.Rels.Elem
import Newbase.Data.List.Rels.Proper

------------
-- Head cons
------------

export
headCons : head (x::xs) = x
headCons = Refl

------------
-- Head elem
------------

export
headElem : {0 xs : List a} -> x = head (x::xs) -> Elem x (x::xs)
headElem Refl = Here
