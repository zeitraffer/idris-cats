module CategoryTheory.Concrete.TypeAsCategory0

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

instance Category0Class Type (~>) where
  getIdentity0 o _ = MkTypeMor id
  getMultiply0 o1 o2 o3 (m12 & m23) = MkTypeMor ((recMor m23) . (recMor m12))

TypeCategory0 : Category0Record
TypeCategory0 = mkCategory0 {to = TypeMorphism}

