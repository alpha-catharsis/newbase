---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.HeadLast

----------
-- imports
----------

import Newbase.Data.List.Ops.Head
import Newbase.Data.List.Ops.Last
import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.Elem
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.Append
import Newbase.Data.List.Theorems.Proper
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.List.Views.SnocList

------------
-- Head cons
------------

public export
headCons : head (x::xs) IsProper = x
headCons = Refl

------------
-- Last cons
------------

public export
lastCons : (0 x : a) -> (0 xs : List a) -> (0 prf : Proper xs) ->
           last (x::xs) IsProper = last xs prf
lastCons _ _ IsProper = Refl

------------
-- Head snoc
------------

public export
headSnoc : (0 x : a) -> (0 xs : List a) -> (0 prf : Proper xs) ->
           head (snoc x xs) (snocProper x xs) = head xs prf
headSnoc _ _ IsProper = Refl

------------
-- Last snoc
------------

public export
lastSnoc : (0 x : a) -> (xs : List a) -> last (snoc x xs) (snocProper x xs) = x
lastSnoc _ []           = Refl
lastSnoc _ [x']         = Refl
lastSnoc x (_::x'::xs') = lastSnoc x (x'::xs')

--------------
-- Head append
--------------

public export
headAppend : (0 xs : List a) -> (0 ys : List a) -> (0 prf : Proper xs) ->
             head (xs ++ ys) (appendProperLeft xs ys prf) = head xs prf
headAppend _ _ IsProper = Refl

--------------
-- Last append
--------------

public export
lastAppend : (xs : List a) -> (0 ys : List a) -> (0 prf : Proper ys) ->
             last (xs ++ ys) (appendProperRight xs ys prf) = last ys prf
lastAppend []           (y'::ys')  IsProper = Refl
lastAppend [x']         (y'::ys')  IsProper = Refl
lastAppend (_::x'::xs') ys         prf      =
  rewrite lastCons x' (xs' ++ ys) (appendProperRight xs' ys prf) in
  lastAppend xs' ys prf

---------------
-- Head reverse
---------------

public export
headReverse : {0 a : Type} -> (xs : List a) -> (0 prf : Proper xs) ->
              head (reverse xs) (reverseProper xs prf) = last xs prf
headReverse (x::xs') IsProper = ?a -- TODO: complete
