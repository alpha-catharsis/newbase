---------------------
-- Module declaration
---------------------

module Newbase.Data.Nat.Theorems.Ord

----------
-- imports
----------

import Newbase.Data.Nat.Rels.LT
import Newbase.Data.Nat.Rels.LTE
import Newbase.Data.Nat.Theorems.Succ

----------------------
-- LT basic properties
----------------------

export
irreflexiveLT : (m : Nat) -> Not (LT m m)
irreflexiveLT Z      LTZero       impossible
irreflexiveLT (S m') (LTSucc prf) = irreflexiveLT m' prf

export
asymmetricLT : LT m n -> Not (LT n m)
asymmetricLT LTZero        LTZero        impossible
asymmetricLT (LTSucc lprf) (LTSucc rprf) = asymmetricLT lprf rprf

export
transitiveLT : LT m n -> LT n o -> LT m o
transitiveLT LTZero        (LTSucc _)    = LTZero
transitiveLT (LTSucc lprf) (LTSucc rprf) = LTSucc (transitiveLT lprf rprf)

export
connectedLT : (m, n : Nat) -> Not (m = n) -> Either (LT m n) (LT n m)
connectedLT Z      Z      contra = void (contra Refl)
connectedLT Z      (S _)  _      = Left LTZero
connectedLT (S _)  Z      _      = Right LTZero
connectedLT (S m') (S n') contra =
  case connectedLT m' n' (noSuccInjective contra) of
    Left lprf  => Left (LTSucc lprf)
    Right rprf => Right (LTSucc rprf)

--------------------
-- LT basic theorems
--------------------

export
bothPredLT : LT (S m) (S n) -> LT m n
bothPredLT LTZero       impossible
bothPredLT (LTSucc prf) = prf

export
rightSuccLT : LT m n -> LT m (S n)
rightSuccLT LTZero       = LTZero
rightSuccLT (LTSucc prf) = LTSucc (rightSuccLT prf)

export
leftPredLT : LT (S m) n -> LT m n
leftPredLT LTZero       impossible
leftPredLT (LTSucc prf) = rightSuccLT prf

export
notBothPredLT : Not (LT (S m) (S n)) -> Not (LT m n)
notBothPredLT contra prf = contra (LTSucc prf)

export
notBothSuccLT : Not (LT m n) -> Not (LT (S m) (S n))
notBothSuccLT contra prf = contra (bothPredLT prf)

export
notRightPredLT : Not (LT m (S n)) -> Not (LT m n)
notRightPredLT contra prf = contra (rightSuccLT prf)

export
notLeftSuccLT : Not (LT m n) -> Not (LT (S m) n)
notLeftSuccLT contra prf = contra (leftPredLT prf)

------------------------
-- LT uninhabited values
------------------------

export
notLTEq : (0 m : Nat) -> Not (LT m m)
notLTEq _      LTZero       impossible
notLTEq (S m') (LTSucc prf) = notLTEq m' prf

export
notLeftSuccRightZeroLT : (0 m : Nat) -> Not (LT (S m) Z)
notLeftSuccRightZeroLT _ _ impossible

-----------------------
-- LTE basic properties
-----------------------

export
reflexiveLTE : (m : Nat) -> LTE m m
reflexiveLTE Z      = LTEZero
reflexiveLTE (S m') = LTESucc (reflexiveLTE m')

export
antisymmetricLTE : LTE m n -> LTE n m -> m = n
antisymmetricLTE LTEZero        LTEZero        = Refl
antisymmetricLTE (LTESucc lprf) (LTESucc rprf) =
 cong S (antisymmetricLTE lprf rprf)

export
transitiveLTE : LTE m n -> LTE n o -> LTE m o
transitiveLTE LTEZero        _              = LTEZero
transitiveLTE (LTESucc lprf) (LTESucc rprf) =
  LTESucc (transitiveLTE lprf rprf)

export
stronglyConnectedLTE : (m, n : Nat) -> Either (LTE m n) (LTE n m)
stronglyConnectedLTE Z _           = Left LTEZero
stronglyConnectedLTE _ Z           = Right LTEZero
stronglyConnectedLTE (S m') (S n') = case stronglyConnectedLTE m' n' of
  Left lprf  => Left (LTESucc lprf)
  Right rprf => Right (LTESucc rprf)

---------------------
-- LTE basic theorems
---------------------

export
bothPredLTE : LTE (S m) (S n) -> LTE m n
bothPredLTE LTEZero       impossible
bothPredLTE (LTESucc prf) = prf

export
rightSuccLTE : LTE m n -> LTE m (S n)
rightSuccLTE LTEZero = LTEZero
rightSuccLTE (LTESucc prf) = LTESucc (rightSuccLTE prf)

export
leftPredLTE : LTE (S m) n -> LTE m n
leftPredLTE LTEZero       impossible
leftPredLTE (LTESucc prf) = rightSuccLTE prf

export
notBothPredLTE : Not (LTE (S m) (S n)) -> Not (LTE m n)
notBothPredLTE contra prf = contra (LTESucc prf)

export
notBothSuccLTE : Not (LTE m n) -> Not (LTE (S m) (S n))
notBothSuccLTE contra prf = contra (bothPredLTE prf)

export
notRightPredLTE : Not (LTE m (S n)) -> Not (LTE m n)
notRightPredLTE contra prf = contra (rightSuccLTE prf)

export
notLeftSuccLTE : Not (LTE m n) -> Not (LTE (S m) n)
notLeftSuccLTE contra prf = contra (leftPredLTE prf)

-------------------------
-- LTE uninhabited values
-------------------------

export
notLTELeftSucc : (0 m : Nat) -> Not (LTE (S m) m)
notLTELeftSucc _      LTEZero       impossible
notLTELeftSucc (S m') (LTESucc prf) = notLTELeftSucc m' prf

export
notLeftSuccRightZeroLTE : (0 m : Nat) -> Not (LTE (S m) Z)
notLeftSuccRightZeroLTE _ _ impossible

-------------------
-- LT/LTE morphisms
-------------------

export
LTtoLTE : LT m n -> LTE m n
LTtoLTE LTZero       = LTEZero
LTtoLTE (LTSucc prf) = LTESucc (LTtoLTE prf)

export
LTEtoLTOrEq : (m, n : Nat) -> LTE m n -> Either (m = n) (LT m n)
LTEtoLTOrEq Z      Z      LTEZero       = Left Refl
LTEtoLTOrEq Z      (S m') LTEZero       = Right LTZero
LTEtoLTOrEq (S m') (S n') (LTESucc prf) = case LTEtoLTOrEq m' n' prf of
  Left eqPrf  => Left (cong S eqPrf)
  Right ltPrf => Right (LTSucc ltPrf)
