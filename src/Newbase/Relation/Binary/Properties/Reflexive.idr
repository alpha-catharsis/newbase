---------------------
-- Module declaration
---------------------

module Newbase.Relation.Binary.Properties.Reflexive

----------
-- Imports
----------

import Newbase.Relation.Binary.Binary

---------------------
-- Reflexive relation
---------------------

public export
Reflexive : {a : Type} -> HRel a -> Type
Reflexive r = {x : a} -> r x x
