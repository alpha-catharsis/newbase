---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.HasLength

--------------------------
-- List length proposition
--------------------------

public export
data HasLength : Nat -> List a -> Type where
  IsEmpty : HasLength 0 []
  IsLonger : HasLength k xs -> HasLength (S k) (x::xs)
