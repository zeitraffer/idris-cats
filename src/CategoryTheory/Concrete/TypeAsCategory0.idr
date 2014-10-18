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

TypeCategory0Full' : Category0FullClass Type (~>)
TypeCategory0Full' = %instance

TypeCategory0Full : Category0FullRecord
TypeCategory0Full = mkCategory0 @{TypeCategory0Full'}

instance Category0ShortClass Type where {}

TypeCategory0Short' : Category0ShortClass Type
TypeCategory0Short' = %instance

TypeCategory0Short : Category0ShortRecord
TypeCategory0Short = mkCategory0 @{TypeCategory0Short'}

