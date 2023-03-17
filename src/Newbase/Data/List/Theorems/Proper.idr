---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Proper

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.HasLength
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.List
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.List.Views.SnocList

-------------------------
-- uninhabited nil proper
-------------------------

notProperNil : Not (Proper [])
notProperNil _ impossible

--------------
-- cons proper
--------------

consProper : Proper (x::xs)
consProper = IsProper

--------------
-- snoc proper
--------------

snocProper : {xs : List a} -> Proper (snoc x xs)
snocProper {xs=[]}     = IsProper
snocProper {xs=x::xs'} = IsProper

----------------
-- append proper
----------------

appendProperLeft : Proper xs -> Proper (xs ++ ys)
appendProperLeft IsProper = IsProper

appendProperRight : {xs : List a} -> Proper ys -> Proper (xs ++ ys)
appendProperRight {xs=[]}     IsProper = IsProper
appendProperRight {xs=x::xs'} IsProper = IsProper

-----------------
-- reverse proper
-----------------

appendReverse : {xs : List a} -> Proper xs -> Proper (reverse xs)
appendReverse {xs=x::xs'} IsProper =
  rewrite reverseOntoExtract [x] xs' in snocProper

