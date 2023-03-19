---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Append

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Ops.Tail

--------------
-- append list
--------------

public export
appendLeftNil : [] ++ xs = xs
appendLeftNil = Refl

public export
appendRightNil : (xs : List a) -> xs ++ [] = xs
appendRightNil []       = Refl
appendRightNil (x::xs') = cong (x::) (appendRightNil xs')

public export
appendAssociative : (xs : List a) -> (0 ys, zs : List a)  ->
                    (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssociative []       _  _  = Refl
appendAssociative (x::xs') ys zs = cong (x::) (appendAssociative xs' ys zs)

public export
appendCons : (xs : List a) -> (0 y : a) -> (0 ys : List a) ->
             xs ++ (y :: ys) = (snoc y xs) ++ ys
appendCons []       _ _  = Refl
appendCons (x::xs') y ys = cong (x::) (appendCons xs' y ys)

public export
consAppend : (x :: xs) ++ ys = x :: (xs ++ ys)
consAppend = Refl
