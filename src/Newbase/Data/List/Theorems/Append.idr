---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Append

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc

--------------
-- list append
--------------

export
appendLeftNil : [] ++ xs = xs
appendLeftNil = Refl

export
appendRightNil : {xs : List a} -> xs ++ [] = xs
appendRightNil {xs=[]}   = Refl
appendRightNil {xs=x::_} = cong (x::) appendRightNil

export
appendAssociative : {xs : List a} -> (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssociative {xs=[]}   = Refl
appendAssociative {xs=x::_} = cong (x::) appendAssociative

export
appendCons : {xs : List a} -> xs ++ (y :: ys) = (snoc y xs) ++ ys
appendCons {xs=[]}   = Refl
appendCons {xs=x::_} = cong (x::) appendCons

export
consAppend : (x :: xs) ++ ys = x :: (xs ++ ys)
consAppend = Refl
