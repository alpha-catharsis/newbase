---------------------
-- Module declaration
---------------------

module Newbase.Relation.Binary.Properties.Symmetric

----------
-- Imports
----------

import Newbase.Relation.Binary.Binary

---------------------
-- Symmetric relation
---------------------

public export
Symmetric : {a : Type} -> HRel a -> Type
Symmetric r = {x, y : a} -> r x y -> r y x
