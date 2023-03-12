---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.HasLength

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.HasLength
import Newbase.Data.List.Theorems.List
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.Nat.Theorems.Plus

----------------
-- exact lenghth
----------------

export
exactLength : HasLength k xs -> length xs = k
exactLength IsEmpty = Refl
exactLength (IsLonger prf) = cong S (exactLength prf)

export
hasLength : (xs : List a) -> length xs = k -> HasLength k xs
hasLength []       Refl = IsEmpty
hasLength (x::xs') Refl = IsLonger (hasLength xs' Refl)

--------------
-- Cons length
--------------

export
consLength : (0 x : a) -> HasLength k xs -> HasLength (S k) (x::xs)
consLength _ = IsLonger

--------------
-- Snoc length
--------------

export
snocLength : (0 x : a) -> (xs : List a) -> HasLength k xs ->
             HasLength (S k) (snoc x xs)
snocLength x []        IsEmpty        = IsLonger IsEmpty
snocLength x (x'::xs') (IsLonger prf) = IsLonger (snocLength x xs' prf)

----------------
-- Append length
----------------

export
appendLength : (xs : List a) -> (ys : List a) -> HasLength j xs ->
               HasLength k ys -> HasLength (j + k) (xs ++ ys)
appendLength []      _         IsEmpty         rprf           = rprf
appendLength xs      []        lprf            IsEmpty        =
  rewrite appendRightNil xs in
  rewrite plusRightZero j in lprf
appendLength (x::xs') (y::ys') (IsLonger lprf) (IsLonger rpf) =
  IsLonger (appendLength xs' (y :: ys') lprf (IsLonger rpf))

-----------------
-- Reverse length
-----------------

export
reverseLength : (xs : List a) -> HasLength w xs -> HasLength w (reverse xs)
reverseLength []       IsEmpty        = IsEmpty
reverseLength (x::xs') (IsLonger prf) =
  rewrite reverseOntoExtract [x] xs' in
  snocLength x (reverse xs') (reverseLength xs' prf)
