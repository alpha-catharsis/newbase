---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.HasLength

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Ops.Tail
import Newbase.Data.List.Rels.HasLength
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.Append
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.Nat.Theorems.Plus

-------------------------
-- uninhabited nil length
-------------------------

public export
notLongNil : Not (HasLength (S k) [])
notLongNil _ impossible

----------------
-- unique length
----------------

public export
lengthUnique : HasLength j xs -> HasLength k xs -> j = k
lengthUnique IsEmpty         IsEmpty         = Refl
lengthUnique (IsLonger lprf) (IsLonger rprf) = cong S (lengthUnique lprf rprf)

---------------
-- exact length
---------------

public export
exactLength : HasLength k xs -> length xs = k
exactLength IsEmpty        = Refl
exactLength (IsLonger prf) = cong S (exactLength prf)

public export
exactLengthRev : (xs : List a) -> (0 k : Nat) -> length xs = k -> HasLength k xs
exactLengthRev []       _                Refl = IsEmpty
exactLengthRev (x::xs') (S (length xs')) Refl =
  IsLonger (exactLengthRev xs' (length xs') Refl)

--------------
-- Cons length
--------------

public export
notEmptyCons : Not (HasLength 0 (x::xs))
notEmptyCons _ impossible

public export
consLengthSame : HasLength k (x::xs) -> HasLength k (y::xs)
consLengthSame (IsLonger IsEmpty)        = IsLonger IsEmpty
consLengthSame (IsLonger (IsLonger prf)) =
  IsLonger (consLengthSame {x} (IsLonger prf))

public export
consLength : HasLength k xs -> HasLength (S k) (x::xs)
consLength = IsLonger

public export
consLengthRev : HasLength (S k) (x::xs) -> HasLength k xs
consLengthRev (IsLonger prf) = prf

public export
consExchangeLength : HasLength k (x::(x'::xs)) -> HasLength k (x'::(x::xs))
consExchangeLength (IsLonger (IsLonger prf)) = IsLonger (IsLonger prf)

--------------
-- Snoc length
--------------

public export
notEmptySnoc : {xs : List a} -> Not (HasLength 0 (snoc x xs))
notEmptySnoc {xs=[]}   _ impossible
notEmptySnoc {xs=_::_} _ impossible

public export
snocLengthSame : {xs : List a} -> HasLength k (snoc x xs) ->
                 HasLength k (snoc y xs)
snocLengthSame {xs=[]}      (IsLonger IsEmpty) = (IsLonger IsEmpty)
snocLengthSame {xs=x'::xs'} (IsLonger prf)     =
  consLength (snocLengthSame prf)

public export
snocLength : HasLength k xs -> HasLength (S k) (snoc x xs)
snocLength IsEmpty        = IsLonger IsEmpty
snocLength (IsLonger prf) = IsLonger (snocLength prf)

public export
consSnocLength : HasLength (S k) (x::xs) -> HasLength (S k) (snoc x' xs)
consSnocLength prf = snocLength (consLengthRev prf)

public export
snocConsLength : {xs : List a} -> HasLength k (snoc x' xs) ->
                 HasLength k (x::xs)
snocConsLength {xs=[]}     (IsLonger IsEmpty) = IsLonger IsEmpty
snocConsLength {xs=x'::xs} (IsLonger prf)     =
  consExchangeLength (consLength (snocConsLength prf))

public export
snocLengthRev : {xs : List a} -> HasLength (S k) (snoc x xs) ->
                HasLength k xs
snocLengthRev {xs=[]}      (IsLonger IsEmpty) = IsEmpty
snocLengthRev {xs=x'::xs'} (IsLonger prf)     = snocConsLength prf

public export
snocExchangeLength : {k : Nat} -> {xs : List a} -> {x' : a} ->
                     HasLength k (snoc x (snoc  x' xs)) ->
                     HasLength k (snoc x' (snoc  x xs))
snocExchangeLength {k=Z}          prf = void (notEmptySnoc prf)
snocExchangeLength {k=(S Z)}      prf = void (notEmptySnoc (snocLengthRev prf))
snocExchangeLength {k=(S (S k'))} prf =
  snocLength (snocLength (snocLengthRev (snocLengthRev prf)))

----------------
-- Append length
----------------

public export
appendLength : HasLength j xs -> HasLength k ys -> HasLength (j + k) (xs ++ ys)
appendLength IsEmpty         rprf           = rprf
appendLength lprf            IsEmpty        = rewrite appendRightNil xs in
                                              rewrite plusRightZero j in lprf
appendLength (IsLonger lprf) (IsLonger rpf) =
  IsLonger (appendLength lprf (IsLonger rpf))

-----------------
-- Reverse length
-----------------

public export
reverseLength : {xs : List a} -> HasLength k xs -> HasLength k (reverse xs)
reverseLength {xs=[]}     IsEmpty        = IsEmpty
reverseLength {xs=x::xs'} (IsLonger prf) =
  rewrite reverseOntoExtract [x] xs' in
  snocLength (reverseLength prf)

-------------------
-- length to proper
-------------------

public export
lengthProper : HasLength (S k) xs -> Proper xs
lengthProper (IsLonger prf) = IsProper

--------------
-- Tail length
--------------

public export
tailLength : (prf : HasLength (S k) xs) ->
             HasLength k (tail xs (lengthProper prf))
tailLength (IsLonger prf) = prf
