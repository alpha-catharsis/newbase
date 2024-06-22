---------------------
-- Module declaration
---------------------

module Newbase.Relation.Binary.Binary

------------------
-- Binary relation
------------------

public export
Rel : Type -> Type -> Type
Rel a b = a -> b -> Type

------------------------------
-- Homogeneous Binary relation
------------------------------

public export
HRel : Type -> Type
HRel a = Rel a a
