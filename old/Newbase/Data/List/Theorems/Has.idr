---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Theorems.Has

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Rels.Elem
import Newbase.Data.List.Rels.Has
import Newbase.Data.List.Rels.Proper
import Newbase.Data.List.Theorems.Append
import Newbase.Data.List.Theorems.Reverse

--------------
-- uninhabited
--------------

public export
notHasNil : Not (Has (S k) e [])
notHasNil _ impossible

-----------
-- Has elem
-----------

public export
hasElem : Has (S k) e xs -> Elem e xs
hasElem (HasNext _)      = Here
hasElem (MissNext prf _) = There (hasElem prf)

public export
notHasElem : Has 0 e xs -> Not (Elem e xs)
notHasElem HasNone             _               impossible
notHasElem (MissNext prf Refl) Here            impossible
notHasElem (MissNext prf _)    (There elemPrf) = notHasElem prf elemPrf

-------------
-- Has proper
-------------

public export
hasProper : Has (S k) e xs -> Proper xs
hasProper (HasNext _)    = IsProper
hasProper (MissNext _ _) = IsProper

-----------
-- cons has
-----------

public export
consHas : Has k e xs -> Has (S k) e (e::xs)
consHas prf = HasNext prf

public export
consMiss : Has k e xs -> Not (e = e') -> Has k e (e'::xs)
consMiss prf contra = MissNext prf contra

-----------
-- snoc has
-----------

public export
snocHas : {xs : List a} -> Has k e xs -> Has (S k) e (snoc e xs)
snocHas {xs=[]}     HasNone               = HasNext HasNone
snocHas {xs=_::xs'} (HasNext prf)         = HasNext (snocHas prf)
snocHas {xs=_::xs'} (MissNext prf contra) = MissNext (snocHas prf) contra

public export
snocMiss : {xs : List a} -> Has k e xs -> Not (e = e') ->Has k e (snoc e' xs)
snocMiss {xs=[]}     HasNone               eqContra = MissNext HasNone eqContra
snocMiss {xs=_::xs'} (HasNext prf)         eqContra =
  HasNext (snocMiss prf eqContra)
snocMiss {xs=_::xs'} (MissNext prf contra) eqContra =
  MissNext (snocMiss prf eqContra) contra

-------------
-- append has
-------------

public export
appendHas : {xs : List a} -> Has j e xs -> Has k e ys ->
            Has (j + k) e (xs ++ ys)
appendHas {xs=[]}      HasNone                 lprf = lprf
appendHas {xs=_::xs'}  (HasNext rprf')         lprf =
  HasNext (appendHas rprf' lprf)
appendHas {xs=_::xs'}  (MissNext rprf' contra) lprf =
  MissNext (appendHas rprf' lprf) contra

--------------
-- reverse has
--------------

public export
reverseHas : {xs : List a} -> Has k e xs -> Has k e (reverse xs)
reverseHas {xs=[]} HasNone = HasNone
reverseHas {xs=e::xs'} (HasNext prf) =
  rewrite reverseOntoExtract [e] xs' in snocHas (reverseHas prf)
reverseHas {xs=e'::xs'} (MissNext prf contra) =
  rewrite reverseOntoExtract [e'] xs' in snocMiss (reverseHas prf) contra
