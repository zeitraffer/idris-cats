module CategoryTheory.Instances.MappingAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

instance Classic0CategoryFullClass MappingOb (~>) where
  getIdentity0 o _ = MkMappingMorphism id
  getMultiply0 o1 o2 o3 (m12 & m23) = MkMappingMorphism ((recMor m23) . (recMor m12))

MappingClassic0CategoryFull' : Classic0CategoryFullClass MappingOb (~>)
MappingClassic0CategoryFull' = %instance

MappingClassic0CategoryFull : Classic0CategoryFullRecord
MappingClassic0CategoryFull = mkClassic0Category @{MappingClassic0CategoryFull'}

instance Classic0CategoryShortClass MappingOb where {}

MappingClassic0CategoryShort' : Classic0CategoryShortClass MappingOb
MappingClassic0CategoryShort' = %instance

MappingClassic0CategoryShort : Classic0CategoryShortRecord
MappingClassic0CategoryShort = mkClassic0Category @{MappingClassic0CategoryShort'}

