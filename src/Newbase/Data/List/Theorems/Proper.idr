---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Proper

----------
-- imports
----------

import Newbase.Data.List.Ops.Init
import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Ops.Tail
import Newbase.Data.List.Rels.HasLength
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.Append
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.List.Views.SnocList

-------------------------
-- uninhabited nil proper
-------------------------

public export
notProperNil : Not (Proper [])
notProperNil _ impossible

--------------
-- cons proper
--------------

public export
consProper : Proper (x::xs)
consProper = IsProper

--------------
-- snoc proper
--------------

public export
snocProper : (0 x : a) -> (xs : List a) -> Proper (snoc x xs)
snocProper _ []       = IsProper
snocProper _ (x::xs') = IsProper

----------------
-- append proper
----------------

public export
appendProperLeft : (0 xs : List a) -> (0 ys : List a) -> (0 prf : Proper xs) ->
                   Proper (xs ++ ys)
appendProperLeft _ _ IsProper = IsProper

public export
appendProperRight : (xs : List a) -> (0 ys : List a) -> (0 prf : Proper ys) ->
                    Proper (xs ++ ys)
appendProperRight []       _ IsProper = IsProper
appendProperRight (x::xs') _ IsProper = IsProper

--------------
-- tail proper
--------------

-- TODO: complete

--------------
-- Init proper
--------------

-- TODO: complete

-----------------
-- reverse proper
-----------------

public export
reverseProper : (xs : List a) -> (0 prf : Proper xs) -> Proper (reverse xs)
reverseProper (x::xs') IsProper =
  rewrite reverseOntoExtract [x] xs' in snocProper x (reverse xs')

