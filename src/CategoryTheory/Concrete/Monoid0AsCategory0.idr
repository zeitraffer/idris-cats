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

Monoid0Category0' : Category0FullClass Monoid0Record (~>)
Monoid0Category0' = %instance

Monoid0Category0 : Category0FullRecord
Monoid0Category0 = mkCategory0 @{Monoid0Category0'}

