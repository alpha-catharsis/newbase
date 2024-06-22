---------------------
-- Module declaration
---------------------

module Newbase.Relation.Binary.Equality

----------
-- Imports
----------

import Newbase.Data.Pair.Pair
import Newbase.Data.Void.Void
import Newbase.Relation.Binary.Binary
import Newbase.Relation.Binary.Properties.Equivalence
import Newbase.Relation.Binary.Properties.Reflexive
import Newbase.Relation.Binary.Properties.Symmetric
import Newbase.Relation.Binary.Properties.Transitive

--------------------
-- Equality relation
--------------------

public export
data Equal : Rel a b where
 [search a b]
 Refl : {0 x : a} -> Equal x x

%name Equal prf

namespace Builtin

  infix 6 ===, ~=~, /=

  public export
  (===) : (x : a) -> (y : a) -> Type
  (===) = Equal

  public export
  (~=~) : (x : a) -> (y : b) -> Type
  (~=~) = Equal

  public export
  (/=) : (x : a) -> (y : b) -> Type
  (/=) x y = Not (x = y)

%inline
public export
rewrite__impl : {0 x, y : a} -> (0 p : _) ->
                (0 rule : x = y) -> (1 val : p y) -> p x
rewrite__impl p Refl prf = prf

%rewrite Equal rewrite__impl

---------------------------------
-- Equality equivalence instances
---------------------------------

%hint
public export
equalRefl : Reflexive Equal
equalRefl = Refl

%hint
public export
equalSymm : Symmetric Equal
equalSymm = \Refl => Refl

%hint
public export
equalTrans : Transitive Equal
equalTrans = \Refl, Refl => Refl

public export
equalEquiv : Equivalence Equal
equalEquiv = mkTriplet equalRefl equalSymm equalTrans
