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
headElem : {xs : List a} -> {auto 0 prf : Proper xs} -> x = head xs -> Elem x xs
headElem {xs=_::_} Refl = Here
