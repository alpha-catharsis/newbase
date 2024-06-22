---------------------
-- Module declaration
---------------------

module Newbase.Function.Identity.Identity

----------
-- Imports
----------

import Newbase.Data.Pair.Dependent
import Newbase.Data.Pair.Pair
import Newbase.Function.Properties.Bijective
import Newbase.Function.Properties.Injective
import Newbase.Function.Properties.Surjective
import Newbase.Relation.Binary.Binary
import Newbase.Relation.Binary.Equality

--------------------
-- Identity function
--------------------

public export
id : a -> a
id x = x

-------------------------------
-- Identity function properties
-------------------------------

idInj : Injective Identity.id
idInj = \Refl => Refl

idSurj : Surjective Identity.id
idSurj = \y => MkDPair y Refl

idBij : Bijective Identity.id
idBij = MkPair idInj idSurj
