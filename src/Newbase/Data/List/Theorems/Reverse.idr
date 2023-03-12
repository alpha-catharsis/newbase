---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Reverse

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Theorems.List

---------------
-- reverse onto
---------------

export
reverseOntoCons : (x : a) -> (xs : List a) -> (ys : List a) ->
                  reverseOnto (x::xs) ys = reverseOnto xs (x :: ys)
reverseOntoCons _ _ _ = Refl

export
reverseOntoSnocLeft : (x : a) -> (xs : List a) -> (ys : List a) ->
                      reverseOnto (snoc x xs) ys = snoc x (reverseOnto xs ys)
reverseOntoSnocLeft _ _  []      = Refl
reverseOntoSnocLeft x xs (y::ys) = reverseOntoSnocLeft x (y :: xs) ys

export
reverseOntoSnocRight : (x : a) -> (xs : List a) -> (ys : List a) ->
                       reverseOnto xs (snoc x ys) = x :: reverseOnto xs ys
reverseOntoSnocRight _ _  []      = Refl
reverseOntoSnocRight x xs (y::ys) = reverseOntoSnocRight x (y :: xs) ys

export
reverseOntoAppendLeft : (xs, ys, zs : List a) ->
                        reverseOnto (xs ++ ys) zs =
                        reverseOnto ys (reverseOnto zs xs)
reverseOntoAppendLeft []       yz zs = Refl
reverseOntoAppendLeft (x::xs') yz zs = reverseOntoAppendLeft xs' yz (x :: zs)

export
reverseOntoAppendRight : (xs, ys, zs : List a) ->
                         reverseOnto xs (ys ++ zs) =
                         reverseOnto (reverseOnto xs ys) zs
reverseOntoAppendRight xs []       zs = Refl
reverseOntoAppendRight xs (y::ys') zs = reverseOntoAppendRight (y :: xs) ys' zs

export
reverseOntoExtract : (xs, ys : List a) ->
                     reverseOnto xs ys = reverseOnto [] ys ++ xs
reverseOntoExtract xs []       = Refl
reverseOntoExtract xs (y::ys') =
  rewrite reverseOntoExtract [y] ys' in
  rewrite appendAssociative (reverseOnto [] ys') [y] xs in
  reverseOntoExtract (y :: xs) ys'

export
reverseReverseOnto : (xs, ys : List a) ->
                     reverse (reverseOnto xs ys) = reverseOnto ys xs
reverseReverseOnto _  []       = Refl
reverseReverseOnto xs (y::ys') = reverseReverseOnto (y::xs) ys'

----------
-- reverse
----------

export
reverseNil : reverse [] = []
reverseNil = Refl

export
reverseCons : (x : a) -> (xs : List a) ->
              reverse (x::xs) = snoc x (reverse xs)
reverseCons _ []        = Refl
reverseCons x (x'::xs') = reverseOntoSnocLeft x [x'] xs'

export
reverseSnoc : (x : a) -> (xs : List a) ->
              reverse (snoc x xs) = x :: reverse xs
reverseSnoc x []        = Refl
reverseSnoc x (x'::xs') = reverseOntoSnocRight x [x'] xs'

export
reverseAppend : (xs, ys : List a) ->
                reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseAppend xs []       = rewrite appendRightNil xs in Refl
reverseAppend xs (y::ys') = rewrite reverseOntoAppendRight [] xs (y :: ys') in
                            reverseOntoExtract (reverseOnto [] xs) (y :: ys')

export
reverseReverse : (xs : List a) -> reverse (reverse xs) = xs
reverseReverse xs = reverseReverseOnto [] xs
