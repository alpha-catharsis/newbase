---------------------
-- Module declaration
---------------------

module Newbase.Data.Void.Void

-----------------
-- Void data type
-----------------

public export
data Void : Type where

-----------
-- Negation
-----------

public export
Not : Type -> Type
Not a = a -> Void
