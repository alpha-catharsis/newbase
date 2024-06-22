---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Prefix

----------
-- imports
----------

import Newbase.Data.List.Ops.Head
import Newbase.Data.List.Ops.Init
import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.Postfix
import Newbase.Data.List.Rels.Prefix
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.Append
import Newbase.Data.List.Theorems.TailInit
import Newbase.Data.List.Theorems.Reverse
import Newbase.Data.List.Views.SnocList

--------------
-- uninhabited
--------------

public export
notPrefixNil : Not (Prefix (x::xs) [])
notPrefixNil _ impossible

public export
notPrefixCons : Not (z = w) -> Not (Prefix (z::xs) (w::xs))
notPrefixCons contra (ConsPrefix _) = contra Refl

----------------
-- Prefix proper
----------------

public export
prefixProper : Prefix xs ys -> Proper xs -> Proper ys
prefixProper (ConsPrefix _) IsProper = IsProper

--------------
-- Cons prefix
--------------

public export
consPrefix : Prefix xs ys -> Prefix (z::xs) (z::ys)
consPrefix = ConsPrefix

public export
consPrefixRev : Prefix (z::xs) (z::ys) -> Prefix xs ys
consPrefixRev (ConsPrefix prf) = prf

--------------
-- Snoc prefix
--------------

public export
snocPrefix : Prefix xs ys -> Prefix xs (snoc z ys)
snocPrefix NilPrefix        = NilPrefix
snocPrefix (ConsPrefix prf) = ConsPrefix (snocPrefix prf)

--------------
-- Init prefix
--------------

public export
initPrefix : {xs : List a} -> (prf : Proper xs) -> Prefix xs ys ->
             Prefix (init xs prf) ys
initPrefix IsProper (ConsPrefix NilPrefix)        = NilPrefix
initPrefix IsProper (ConsPrefix (ConsPrefix prf)) =
  ConsPrefix (initPrefix IsProper (ConsPrefix prf))

public export
initPrefixBoth : (xs : List a) -> (ys : List a) -> (prf : Proper xs) -> (pofx : Prefix xs ys) ->
                 Prefix (init xs prf) (init ys (prefixProper pofx prf))
initPrefixBoth [_]          [_]          IsProper (ConsPrefix NilPrefix)        =
   NilPrefix
initPrefixBoth [_]          (_::_::_)    IsProper _                             =
   NilPrefix
initPrefixBoth (_::_::_)    [_]          IsProper (ConsPrefix prf)              =
   void (notPrefixNil prf)
initPrefixBoth (_::z'::xs') (_::z'::ys') IsProper (ConsPrefix (ConsPrefix prf)) =
  consPrefix (initPrefixBoth (z'::xs') (z'::ys') IsProper (ConsPrefix prf))

--------------
-- Head prefix
--------------

public export
headPrefix : (prf : Proper xs) -> (pofx : Prefix xs ys) ->
             head xs prf = head ys (prefixProper pofx prf)
headPrefix IsProper (ConsPrefix _) = Refl

----------------
-- Append prefix
----------------

public export
appendLeftPrefix : (zs : List a) -> Prefix xs ys -> Prefix (zs ++ xs) (zs ++ ys)
appendLeftPrefix []       prf      = prf
appendLeftPrefix (_::zs') prf      = ConsPrefix (appendLeftPrefix zs' prf)

public export
appendRightPrefix : Prefix xs ys -> Prefix xs (ys ++ zs)
appendRightPrefix NilPrefix        = NilPrefix
appendRightPrefix (ConsPrefix prf) = ConsPrefix (appendRightPrefix prf)

----------------
-- Revese prefix
----------------

public export
reversePrefix : {xs : List a} -> {ys : List a} -> Prefix xs ys ->
                Postfix (reverse xs) (reverse ys)
reversePrefix                         NilPrefix        = NilPostfix
reversePrefix {xs=z::xs'} {ys=z::ys'} (ConsPrefix prf) =
  rewrite reverseOntoExtract [z] xs' in
  rewrite reverseOntoExtract [z] ys' in SnocPostfix (reversePrefix prf)
