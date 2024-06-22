---------------------
-- Module declaration
---------------------

module Newbase.Relation.Binary.Properties.Equivalence

----------
-- Imports
----------

import Newbase.Data.Pair.Pair
import Newbase.Relation.Binary.Binary
import Newbase.Relation.Binary.Properties.Reflexive
import Newbase.Relation.Binary.Properties.Symmetric
import Newbase.Relation.Binary.Properties.Transitive

-----------------------
-- Equivalence relation
-----------------------

public export
Equivalence : {a : Type} -> HRel a -> Type
Equivalence r = Triplet (Reflexive r) (Symmetric r) (Transitive r)
