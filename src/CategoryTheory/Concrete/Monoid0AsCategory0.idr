module CategoryTheory.Concrete.Monoid0AsCategory0

------------------------------------------------------------

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.Monoid0AsRelation

%access public
%default total

------------------------------------------------------------

instance Category0FullClass Monoid0Record (~>) where
  getIdentity0 o _ = MkMonoid0Morphism id
  getMultiply0 o1 o2 o3 (m12 & m23) = MkMonoid0Morphism ((recMor m23) . (recMor m12))

Monoid0Category0Full' : Category0FullClass Monoid0Record (~>)
Monoid0Category0Full' = %instance

Monoid0Category0Full : Category0FullRecord
Monoid0Category0Full = mkCategory0 @{Monoid0Category0Full'}

instance Category0ShortClass Monoid0Record where {}

Monoid0Category0Short' : Category0ShortClass Monoid0Record
Monoid0Category0Short' = %instance

Monoid0Category0Short : Category0ShortRecord
Monoid0Category0Short = mkCategory0 @{Monoid0Category0Short'}

