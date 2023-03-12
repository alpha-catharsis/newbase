---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Elem

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.Elem
import Newbase.Data.List.Theorems.List
import Newbase.Data.List.Theorems.Reverse

--------------
-- uninhabited
--------------

export
notElemNil : Not (Elem e [])
notElemNil _ impossible

---------------
-- Cons element
---------------

export
consElem : Elem x (x::xs)
consElem = Here

export
consElemEither : Elem e (x::xs) -> Either (e = x) (Elem e xs)
consElemEither Here        = Left Refl
consElemEither (There prf) = Right prf

export
notConsElem : Not (e = x) -> Not (Elem e xs) -> Not (Elem e (x::xs))
notConsElem eqContra elemContra prf = case consElemEither prf of
  Left eqPrf => eqContra eqPrf
  Right prf' => elemContra prf'

---------------
-- Snoc elem
---------------

export
snocElem : (0 e : a) -> (xs : List a) -> Elem e (snoc e xs)
snocElem _ [] = Here
snocElem e (_::xs') = There (snocElem e xs')

export
snocElemEither : (0 e : a) -> (0 x : a) -> (xs : List a) ->
                 Elem e (snoc x xs) -> Either (e = x) (Elem e xs)
snocElemEither _ _ []       Here        = Left Refl
snocElemEither _ _ (_::_)   Here        = Right Here
snocElemEither e x (_::xs') (There prf) = case snocElemEither e x xs' prf of
  Left eqPrf => Left eqPrf
  Right prf' => Right (There prf')

export
notSnocElem : (0 e : a) -> (0 x : a) -> (xs : List a) -> Not (e = x) ->
              Not (Elem e xs) -> Not (Elem e (snoc x xs))
notSnocElem e x xs eqContra elemContra prf =
  case snocElemEither e x xs prf of
    Left eqPrf => eqContra eqPrf
    Right prf' => elemContra prf'

--------------
-- Append elem
--------------

export
appendLeftElem : (0 e : a) -> (0 xs : List a) -> (ys : List a) ->
                 Elem e xs -> Elem e (xs ++ ys)
appendLeftElem _ xs       []       prf         =
  rewrite appendRightNil xs in prf
appendLeftElem _ (_::_)   (_::_)   Here        = Here
appendLeftElem e (_::xs') (y::ys') (There prf) =
  There (appendLeftElem e xs' (y :: ys') prf)

export
appendRightElem : (0 e : a) -> (xs : List a) -> (0 ys : List a) ->
                  Elem e ys -> Elem e (xs ++ ys)
appendRightElem _ []       _  prf = prf
appendRightElem e (_::xs') ys prf = There (appendRightElem e xs' ys prf)

export
appendElemEither : (0 e :a) -> (xs : List a) -> (0 ys : List a) ->
                   Elem e (xs ++ ys) -> Either (Elem e xs) (Elem e ys)
appendElemEither _ []       _  prf         = Right prf
appendElemEither _ (_::_)   _  Here        = Left Here
appendElemEither e (_::xs') ys (There prf) =
  case appendElemEither e xs' ys prf of
    Left lprf => Left (There lprf)
    Right rprf => Right rprf

export
notAppendElem : (0 e :a) -> (xs : List a) -> (0 ys : List a) ->
                Not (Elem e xs) -> Not (Elem e ys) -> Not (Elem e (xs ++ ys))
notAppendElem e xs ys lcontra rcontra prf =
  case appendElemEither e xs ys prf of
    Left lprf => lcontra lprf
    Right rprf => rcontra rprf

---------------
-- Reverse elem
---------------

export
reverseElem : (0 e : a) -> (xs : List a) -> Elem e xs -> Elem e (reverse xs)
reverseElem e (e::xs') Here        = rewrite reverseOntoExtract [e] xs' in
                                     snocElem e (reverse xs')
reverseElem e (x::xs') (There prf) = rewrite reverseOntoExtract [x] xs' in
                                     appendLeftElem e (reverse xs') [x]
                                                    (reverseElem e xs' prf)
