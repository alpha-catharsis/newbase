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
exactLengthRev : (xs : List a) -> length xs = k -> HasLength k xs
exactLengthRev []       Refl = IsEmpty
exactLengthRev (x::xs') Refl = IsLonger (exactLengthRev xs' Refl)

--------------
-- Cons length
--------------

export
consLength : HasLength k xs -> HasLength (S k) (x::xs)
consLength = IsLonger

export
consLengthRev : HasLength (S k) (x::xs) -> HasLength k xs
consLengthRev (IsLonger prf) = prf

export
consLengthSame : HasLength k (x::xs) -> HasLength k (y::xs)
consLengthSame (IsLonger IsEmpty) = IsLonger IsEmpty
consLengthSame (IsLonger (IsLonger prf)) =
  IsLonger (consLengthSame {x} (IsLonger prf))

--------------
-- Snoc length
--------------

export
snocLength : HasLength k xs -> HasLength (S k) (snoc x xs)
snocLength IsEmpty        = IsLonger IsEmpty
snocLength (IsLonger prf) = IsLonger (snocLength prf)

export
snocLengthRev : (xs : List a) -> HasLength (S k) (snoc x xs) -> HasLength k xs
snocLengthRev []        prf = consLengthRev prf
snocLengthRev (x'::xs') (IsLonger prf) = ?TODO -- TODO: complete

----------------
-- Append length
----------------

export
appendLength : HasLength j xs -> HasLength k ys -> HasLength (j + k) (xs ++ ys)
appendLength IsEmpty         rprf           = rprf
appendLength lprf            IsEmpty        = rewrite appendRightNil xs in
                                              rewrite plusRightZero j in lprf
appendLength (IsLonger lprf) (IsLonger rpf) =
  IsLonger (appendLength lprf (IsLonger rpf))

-----------------
-- Reverse length
-----------------

export
reverseLength : (xs : List a) -> HasLength k xs -> HasLength k (reverse xs)
reverseLength []       IsEmpty        = IsEmpty
reverseLength (x::xs') (IsLonger prf) =
  rewrite reverseOntoExtract [x] xs' in
  snocLength (reverseLength xs' prf)
