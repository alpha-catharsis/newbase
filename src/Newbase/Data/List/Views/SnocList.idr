---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Views.SnocList

----------
-- imports
----------

import Newbase.Data.List.Ops.Snoc
import Newbase.Data.List.Theorems.List

----------------
-- SnocList view
----------------


public export
data SnocList : List a -> Type where
  Nil : SnocList []
  Snoc : (x : a) -> (xs : List a) -> SnocList xs -> SnocList (snoc x xs)

export
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Nil xs
  where snocListHelp : {left : List a} -> SnocList left -> (right : List a) ->
                       SnocList (left ++ right)
        snocListHelp snoc []        = rewrite appendRightNil left in snoc
        snocListHelp snoc (x :: xs) =
          rewrite sym (appendAssociative left [x] xs) in
          snocListHelp (Snoc x left snoc) xs
