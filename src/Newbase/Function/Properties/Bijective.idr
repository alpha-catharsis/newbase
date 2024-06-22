---------------------
-- Module declaration
---------------------

module Newbase.Function.Properties.Bijective

----------
-- Imports
----------

import Newbase.Data.Pair.Dependent
import Newbase.Data.Pair.Pair
import Newbase.Function.Properties.Injective
import Newbase.Function.Properties.Surjective
import Newbase.Relation.Binary.Equality

---------------------
-- Bijective property
---------------------

public export
Bijective : {a, b : Type} -> (a -> b) -> Type
Bijective f = Pair (Injective f) (Surjective f)
