module CategoryTheory.Concrete.TypeAsCategory0

------------------------------------------------------------

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

instance Category0FullClass Type (~>) where
  getIdentity0 o _ = MkTypeMorphism id
  getMultiply0 o1 o2 o3 (m12 & m23) = MkTypeMorphism ((recMor m23) . (recMor m12))

TypeCategory0' : Category0FullClass Type (~>)
TypeCategory0' = %instance

TypeCategory0 : Category0FullRecord
TypeCategory0 = mkCategory0 @{TypeCategory0'}

