---------------------
-- Module declaration
---------------------

module Newbase.Function.Properties.Injective

----------
-- Imports
----------

import Newbase.Relation.Binary.Equality

---------------------
-- Injective property
---------------------

public export
Injective : {a, b : Type} -> (a -> b) -> Type
Injective f = {x1, x2 : a} -> f x1 = f x2 -> x1 = x2
