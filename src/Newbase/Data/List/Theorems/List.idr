---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.List

--------------
-- list append
--------------

export
appendLeftNil : (0 xs : List a) -> [] ++ xs = xs
appendLeftNil _ = Refl

export
appendRightNil : (xs : List a) -> xs ++ [] = xs
appendRightNil []         = Refl
appendRightNil (x :: xs') = cong (x::) (appendRightNil xs')

export
appendAssociative : (xs, ys, zs : List a) ->
                    (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssociative []       ys zs = Refl
appendAssociative (x::xs') ys zs = cong (x::) (appendAssociative  xs' ys zs)

export
appendCons : (xs : List a) -> (y : a) -> (ys : List a) ->
             xs ++ (y :: ys) = (xs ++ [y]) ++ ys
appendCons []      y ys = Refl
appendCons (x::xs) y ys = cong (x::) (appendCons xs y ys)
