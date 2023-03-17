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
reverseOntoCons : reverseOnto (x::xs) ys = reverseOnto xs (x::ys)
reverseOntoCons = Refl

export
reverseOntoSnocLeft : {ys : List a} -> reverseOnto (snoc x xs) ys =
                                       snoc x (reverseOnto xs ys)
reverseOntoSnocLeft {ys=[]}   = Refl
reverseOntoSnocLeft {ys=_::_} = reverseOntoSnocLeft

export
reverseOntoSnocRight : {ys : List a} -> reverseOnto xs (snoc x ys) =
                                        x::reverseOnto xs ys
reverseOntoSnocRight {ys=[]}   = Refl
reverseOntoSnocRight {ys=_::_} = reverseOntoSnocRight

export
reverseOntoAppendLeft : {xs : List a} -> reverseOnto (xs ++ ys) zs =
                                         reverseOnto ys (reverseOnto zs xs)
reverseOntoAppendLeft {xs=[]}   = Refl
reverseOntoAppendLeft {xs=x::_} = reverseOntoAppendLeft {zs=x::zs}

export
reverseOntoAppendRight : {ys : List a} -> reverseOnto xs (ys ++ zs) =
                                          reverseOnto (reverseOnto xs ys) zs
reverseOntoAppendRight {ys=[]}   = Refl
reverseOntoAppendRight {ys=_::_} = reverseOntoAppendRight

export
reverseOntoExtract : {ys : List a} -> reverseOnto xs ys =
                                      reverseOnto [] ys ++ xs
reverseOntoExtract {ys=[]}     = Refl
reverseOntoExtract {ys=y::ys'} =
  rewrite reverseOntoExtract {xs=[y]} {ys=ys'} in
  rewrite appendAssociative (reverseOnto [] ys') [y] xs in reverseOntoExtract

export
reverseReverseOnto : {ys : List a} -> reverse (reverseOnto xs ys) =
                                      reverseOnto ys xs
reverseReverseOnto {ys=[]}   = Refl
reverseReverseOnto {ys=_::_} = reverseReverseOnto

----------
-- reverse
----------

export
reverseNil : reverse [] = []
reverseNil = Refl

export
reverseCons : {xs : List a} -> reverse (x::xs) = snoc x (reverse xs)
reverseCons {xs=[]}   = Refl
reverseCons {xs=_::_} = reverseOntoSnocLeft

export
reverseSnoc : {xs : List a} -> reverse (snoc x xs) = x::reverse xs
reverseSnoc {xs=[]}    = Refl
reverseSnoc {xs=_::_} = reverseOntoSnocRight

export
reverseAppend : {ys : List a} -> reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseAppend {ys=[]}     = rewrite appendRightNil xs in Refl
reverseAppend {ys=y::ys'} =
  rewrite reverseOntoAppendRight {xs=[]} {ys=xs} {zs=y::ys'} in
  reverseOntoExtract {ys=y::ys'}

export
reverseReverse : {xs : List a} -> reverse (reverse xs) = xs
reverseReverse = reverseReverseOnto
