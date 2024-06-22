---------------------
-- Module declaration
---------------------

module Newbase.Data.Fin.Theorems.Fin

----------
-- imports
----------

import Newbase.Data.Fin.Fin
import Newbase.Data.Nat.Rels.LT

-------------------------
-- Fin uninhabited values
-------------------------

xyz : Not (Fin 0)
xyz (MkFin _ _) impossible
