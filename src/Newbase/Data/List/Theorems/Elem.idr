---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Elem

----------
-- imports
----------

import Newbase.Data.List.Ops.Head
import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.Elem
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.Append
import Newbase.Data.List.Theorems.Reverse

--------------
-- uninhabited
--------------

public export
notElemNil : Not (Elem e [])
notElemNil _ impossible

------------
-- Head elem
------------

public export
headElem : (0 x : a) -> (xs : List a) -> (0 prf : Proper xs) ->
           x = head xs prf -> Elem x xs
headElem _ (_::_) IsProper Refl = Here

---------------
-- Cons element
---------------

public export
consElem : Elem x (x::xs)
consElem = Here

public export
consElemEither : Elem e (x::xs) -> Either (e = x) (Elem e xs)
consElemEither Here        = Left Refl
consElemEither (There prf) = Right prf

public export
notConsElem : Not (e = x) -> Not (Elem e xs) -> Not (Elem e (x::xs))
notConsElem eqContra elemContra prf = case consElemEither prf of
  Left eqPrf => eqContra eqPrf
  Right prf' => elemContra prf'

------------
-- Snoc elem
------------

public export
snocElem : {xs : List a} -> Elem e (snoc e xs)
snocElem {xs=[]}   = Here
snocElem {xs=_::_} = There snocElem

public export
snocElemEither : {xs : List a} -> Elem e (snoc x xs) ->
                 Either (e = x) (Elem e xs)
snocElemEither {xs=[]}   Here        = Left Refl
snocElemEither {xs=_::_} Here        = Right Here
snocElemEither {xs=_::_} (There prf) = case snocElemEither prf of
  Left eqPrf => Left eqPrf
  Right prf' => Right (There prf')

public export
notSnocElem : {xs : List a} -> Not (e = x) -> Not (Elem e xs) ->
              Not (Elem e (snoc x xs))
notSnocElem eqContra elemContra prf = case snocElemEither prf of
    Left eqPrf => eqContra eqPrf
    Right prf' => elemContra prf'

--------------
-- Append elem
--------------

public export
appendLeftElem : {ys : List a} -> Elem e xs -> Elem e (xs ++ ys)
appendLeftElem {ys=[]}     prf       = rewrite appendRightNil xs in prf
appendLeftElem {ys=_::_}  Here       = Here
appendLeftElem {ys=_::_} (There prf) = There (appendLeftElem prf)

public export
appendRightElem : {xs : List a} -> Elem e ys -> Elem e (xs ++ ys)
appendRightElem {xs=[]}   prf = prf
appendRightElem {xs=_::_} prf = There (appendRightElem prf)

public export
appendElemEither : {xs : List a} -> Elem e (xs ++ ys) ->
                   Either (Elem e xs) (Elem e ys)
appendElemEither {xs=[]}   prf         = Right prf
appendElemEither {xs=_::_} Here        = Left Here
appendElemEither {xs=_::_} (There prf) = case appendElemEither prf of
    Left lprf => Left (There lprf)
    Right rprf => Right rprf

public export
notAppendElem : {xs : List a} -> Not (Elem e xs) -> Not (Elem e ys) ->
                Not (Elem e (xs ++ ys))
notAppendElem lcontra rcontra prf = case appendElemEither prf of
    Left lprf => lcontra lprf
    Right rprf => rcontra rprf

---------------
-- Reverse elem
---------------

public export
reverseElem : {xs : List a} -> Elem e xs -> Elem e (reverse xs)
reverseElem {xs=e::xs'} Here        =
  rewrite reverseOntoExtract [e] xs' in snocElem
reverseElem {xs=x::xs'} (There prf) =
  rewrite reverseOntoExtract [x] xs' in appendLeftElem (reverseElem prf)
