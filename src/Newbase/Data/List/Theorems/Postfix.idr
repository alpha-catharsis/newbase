---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Postfix

----------
-- imports
----------

import Newbase.Data.List.Ops.Last
import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Ops.Tail
import Newbase.Data.List.Rels.Postfix
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.HeadLast
import Newbase.Data.List.Views.SnocList

--------------
-- uninhabited
--------------

-- public export
-- notPostfix : Not (Postfix (x::xs) [])
-- notPostfix _ impossible

-----------------
-- Postfix proper
-----------------

-- public export
-- postfixProper : Postfix xs ys -> Proper xs -> Proper ys
-- postfixProper SamePostfix       IsProper = IsProper
-- postfixProper (PostfixNext prf) IsProper = IsProper

---------------
-- Cons postfix
---------------

-- public export
-- consPostfix : Postfix xs ys -> Postfix xs (e::ys)
-- consPostfix prf = PostfixNext prf

-- public export
-- consPostfixRev : Postfix (e::xs) ys -> Postfix xs ys
-- consPostfixRev SamePostfix       = PostfixNext SamePostfix
-- consPostfixRev (PostfixNext prf) = PostfixNext (consPostfixRev prf)

---------------
-- Snoc postfix
---------------

-- public export
-- snocPostfix : Postfix xs ys -> Postfix (snoc e xs) (snoc e ys)
-- snocPostfix SamePostfix       = SamePostfix
-- snocPostfix (PostfixNext prf) = PostfixNext (snocPostfix prf)

---------------
-- Tail postfix
---------------

-- public export
-- tailPostfix : (prf : Proper xs) -> Postfix xs ys -> Postfix (tail xs prf) ys
-- tailPostfix IsProper SamePostfix       = PostfixNext SamePostfix
-- tailPostfix IsProper (PostfixNext prf) = consPostfix (consPostfixRev prf)

-- public export
-- tailPostfixBoth : (prf : Proper xs) -> (pofx : Postfix xs ys) ->
--                   Postfix (tail xs xprf) (tail ys (postfixProper pofx prf))
-- tailPostfixBoth IsProper SamePostfix       = SamePostfix
-- tailPostfixBoth IsProper (PostfixNext prf) = consPostfixRev prf

---------------
-- Last postfix
---------------

-- public export
-- lastPostfix : {xs : List a} -> {ys : List a} -> (prf : Proper xs) ->
--               (pofx : Postfix xs ys) ->
--               last xs prf = last ys (postfixProper pofx prf)
-- lastPostfix IsProper SamePostfix = Refl
-- lastPostfix IsProper (PostfixNext SamePostfix) = ?e
-- lastPostfix IsProper (PostfixNext (PostfixNext prf')) = ?f

-----------------
-- Append postfix
-----------------

-- public export
-- appendLeftPostfix : (zs : List a) -> Postfix xs ys -> Postfix xs (zs ++ ys)
-- appendLeftPostfix []       SamePostfix       = SamePostfix
-- appendLeftPostfix (z::zs') SamePostfix       =
--   PostfixNext (appendLeftPostfix zs' SamePostfix)
-- appendLeftPostfix []       (PostfixNext prf) = PostfixNext prf
-- appendLeftPostfix (z::zs') (PostfixNext prf) =
--   PostfixNext (appendLeftPostfix zs' (PostfixNext prf))

-- public export
-- appendRightPostfix : Postfix xs ys -> Postfix (xs ++ zs) (ys ++ zs)
-- appendRightPostfix SamePostfix       = SamePostfix
-- appendRightPostfix (PostfixNext prf) = PostfixNext (appendRightPostfix prf)
