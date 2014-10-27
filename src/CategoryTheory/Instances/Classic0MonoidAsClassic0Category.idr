module CategoryTheory.Instances.Classic0MonoidAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Instances.Classic0MonoidAsGraph

%access public
%default total

------------------------------------------------------------

instance Classic0CategoryFullClass Classic0MonoidRecord (|~>|) 
  where
    getIdentity0 o _ = MkClassic0MonoidMorphism id
    getMultiply0 o1 o2 o3 (m12 & m23) = MkClassic0MonoidMorphism ((recMor m23) . (recMor m12))

Classic0MonoidClassic0CategoryFull' : Classic0CategoryFullClass Classic0MonoidRecord (|~>|)
Classic0MonoidClassic0CategoryFull' = %instance

Classic0MonoidClassic0CategoryFull : Classic0CategoryFullRecord
Classic0MonoidClassic0CategoryFull = mkClassic0Category @{Classic0MonoidClassic0CategoryFull'}

instance Classic0CategoryShortClass Classic0MonoidRecord 
  where {}

Classic0MonoidClassic0CategoryShort' : Classic0CategoryShortClass Classic0MonoidRecord
Classic0MonoidClassic0CategoryShort' = %instance

Classic0MonoidClassic0CategoryShort : Classic0CategoryShortRecord
Classic0MonoidClassic0CategoryShort = mkClassic0Category @{Classic0MonoidClassic0CategoryShort'}

