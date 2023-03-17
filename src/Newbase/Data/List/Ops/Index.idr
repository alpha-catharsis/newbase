---------------------
-- Module declaration
---------------------

module Newbase.Data.List.Ops.Index

----------
-- imports
----------

import Newbase.Data.Fin.Fin
import Newbase.Data.List.Rels.HasLength
import Newbase.Data.Nat.Rels.LT
import Newbase.Data.Nat.Theorems.Ord

-------------
-- List index
-------------

public export
index : (xs : List a) -> (0 prf : HasLength k xs) -> (idx : Fin k) -> a
index []       IsEmpty            (MkFin _ _)            impossible
index (x::_)   _                  (MkFin Z _)            = x
index (x::xs') (IsLonger longprf) (MkFin (S nidx) ltprf) =
  index xs' longprf (MkFin nidx (bothPredLT ltprf))
