---------------------
-- Module declaration
---------------------

module Newbase.Function.Properties.Surjective

----------
-- Imports
----------

import Newbase.Data.Pair.Dependent
import Newbase.Relation.Binary.Equality

----------------------
-- Surjective property
----------------------

public export
Surjective : {a, b : Type} -> (a -> b) -> Type
Surjective f = (y : b) -> DPair a (\x => x = y)
