---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.TailInit

----------
-- imports
----------

import Newbase.Data.List.Ops.Head
import Newbase.Data.List.Ops.Init
import Newbase.Data.List.Ops.Last
import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Ops.Tail
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.HeadLast
import Newbase.Data.List.Theorems.Proper
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.List.Views.SnocList

------------
-- Tail cons
------------

public export
tailCons : tail (x::xs) IsProper = xs
tailCons = Refl

------------
-- Tail snoc
------------

public export
tailSnoc : (0 x : a) -> (0 xs : List a) -> (0 prf : Proper xs) ->
           tail (snoc x xs) (snocProper x xs) = snoc x (tail xs prf)
tailSnoc _ (_::_) IsProper = Refl

------------
-- Init cons
------------

public export
initCons : (0 x : a) -> (0 xs : List a) -> (0 prf : Proper xs) ->
           init (x::xs) IsProper = x::init xs prf
initCons _ (_::_) IsProper = Refl

------------
-- Init snoc
------------

public export
initSnoc : (0 x : a) -> (xs : List a) ->
           init (snoc x xs) (snocProper x xs) = xs
initSnoc _ []        = Refl
initSnoc x (x'::xs') = rewrite initCons x' (snoc x xs') (snocProper x xs') in
                       cong (x'::) (initSnoc x xs')

-----------------
-- Head/Tail cons
-----------------

public export
headTailCons : (0 prf : Proper xs) -> head xs prf::tail xs prf = xs
headTailCons IsProper = Refl

-----------------
-- Last/Init snoc
-----------------

public export
lastInitSnoc : (xs : List a) -> (0 prf : Proper xs) ->
               snoc (last xs prf) (init xs prf) = xs
lastInitSnoc (x::xs') IsProper with (snocList xs')
  lastInitSnoc [x]                 IsProper | Nil            = Refl
  lastInitSnoc (x::(xs'' ++ [x'])) IsProper | Snoc x' xs'' _ =
    rewrite initCons x (xs'' ++ [x']) (snocProper x' xs'') in
    rewrite initSnoc x' xs'' in
    rewrite lastSnoc x' (x::xs'') in Refl

--------------
-- Tail append
--------------

public export
tailAppend : (0 xs : List a) -> (0 ys : List a) -> (0 prf : Proper xs) ->
             tail (xs ++ ys) (appendProperLeft xs ys prf) = tail xs prf ++ ys
tailAppend (_::_) _ IsProper = Refl

--------------
-- Init append
--------------

public export
initAppend : (xs : List a) -> (0 ys : List a) -> (0 prf : Proper ys) ->
             init (xs ++ ys) (appendProperRight xs ys prf) = xs ++ init ys prf
initAppend []       (_::_)   IsProper = Refl
initAppend (x::xs') (y::ys') IsProper =
  rewrite initCons x (xs' ++ (y::ys'))
                   (appendProperRight xs' (y::ys') IsProper) in
  cong (x::) (initAppend xs' (y :: ys') IsProper)

---------------
-- Tail Reverse
---------------

public export
tailReverse : (xs : List a) -> (prf : Proper xs) ->
              tail (reverse xs) (reverseProper xs prf) = reverse (init xs prf)
tailReverse (x::xs') IsProper with (snocList xs')
  tailReverse [x]                 IsProper | Nil            = Refl
  tailReverse (x::(xs'' ++ [x'])) IsProper | Snoc x' xs'' _ =
    rewrite reverseOntoSnocRight x' [] xs'' in
    rewrite reverseOntoExtract [x] (snoc x' xs'') in
    rewrite reverseOntoSnocRight x' [] xs'' in
    rewrite initSnoc x' (x::xs'') in
    rewrite reverseOntoExtract [x] xs'' in Refl

---------------
-- Init Reverse
---------------

public export
initReverse : (xs : List a) -> (prf : Proper xs) ->
              init (reverse xs) (reverseProper xs prf) = reverse (tail xs prf)
initReverse (x::xs') IsProper with (snocList xs')
  initReverse [x]                 IsProper | Nil            = Refl
  initReverse (x::(xs'' ++ [x'])) IsProper | Snoc x' xs'' _ =
    rewrite reverseOntoSnocRight x' [] xs'' in
    rewrite reverseOntoExtract [x] (snoc x' xs'') in
    rewrite reverseOntoSnocRight x' [] xs'' in
    rewrite initSnoc x (x'::reverse xs'') in Refl
