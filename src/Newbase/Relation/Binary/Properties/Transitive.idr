---------------------
-- Module declaration
---------------------

module Newbase.Relation.Binary.Properties.Transitive

----------
-- Imports
----------

import Newbase.Relation.Binary.Binary

----------------------
-- Transitive relation
----------------------

public export
Transitive : {a : Type} -> HRel a -> Type
Transitive r = {x, y, z : a} -> r x y -> r y z -> r x z
