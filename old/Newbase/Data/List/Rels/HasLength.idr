---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Rels.HasLength

--------------------------
-- List length proposition
--------------------------

public export
data HasLength : (0 k : Nat) -> (0 xs : List a) -> Type where
  IsEmpty : HasLength 0 []
  IsLonger : HasLength k xs -> HasLength (S k) (x::xs)

