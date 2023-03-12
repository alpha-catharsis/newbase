---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Reverse

--------------------
-- List reverse onto
--------------------

public export
reverseOnto' : List a -> List a -> List a
reverseOnto' xs [] = xs
reverseOnto' xs (y::ys) = reverseOnto' (y::xs) ys

---------------
-- List reverse
---------------

public export
reverse' : List a -> List a
reverse' = reverseOnto' []

