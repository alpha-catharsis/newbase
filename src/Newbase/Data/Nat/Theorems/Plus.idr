---------------------
-- Module declaration
---------------------

module Newbase.Data.Nat.Theorems.Plus

------------
-- Plus zero
------------

export
plusLeftZero : (0 m : Nat) -> 0 + m = m
plusLeftZero _ = Refl

export
plusRightZero : (m : Nat) -> m + 0 = m
plusRightZero Z      = Refl
plusRightZero (S m') = cong S (plusRightZero m')

-----------
-- Plus one
-----------

export
plusLeftOne : (0 m : Nat) -> 1 + m = S m
plusLeftOne _ = Refl

export
plusRightOne : (m : Nat) -> m + 1 = S m
plusRightOne Z      = Refl
plusRightOne (S m') = cong S (plusRightOne m')
