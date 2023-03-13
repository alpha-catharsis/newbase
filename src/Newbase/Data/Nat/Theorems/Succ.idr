---------------------
-- Module declaration
---------------------

module Newbase.Data.Nat.Theorems.Succ

-------------------
-- Succ injectivity
-------------------

export
succInjective : S m = S n -> m = n
succInjective Refl = Refl

export
noSuccInjective : Not (S m = S n) -> Not (m = n)
noSuccInjective contra prf = contra (cong S prf)
