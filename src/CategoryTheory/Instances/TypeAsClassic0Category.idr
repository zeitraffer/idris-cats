module CategoryTheory.Instances.TypeAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

instance Classic0CategoryFullClass Type (~>) where
  getIdentity0 o _ = MkTypeMapping id
  getMultiply0 o1 o2 o3 (m12 & m23) = MkTypeMapping ((recMor m23) . (recMor m12))

TypeClassic0CategoryFull' : Classic0CategoryFullClass Type (~>)
TypeClassic0CategoryFull' = %instance

TypeClassic0CategoryFull : Classic0CategoryFullRecord
TypeClassic0CategoryFull = mkClassic0Category @{TypeClassic0CategoryFull'}

instance Classic0CategoryShortClass Type where {}

TypeClassic0CategoryShort' : Classic0CategoryShortClass Type
TypeClassic0CategoryShort' = %instance

TypeClassic0CategoryShort : Classic0CategoryShortRecord
TypeClassic0CategoryShort = mkClassic0Category @{TypeClassic0CategoryShort'}

