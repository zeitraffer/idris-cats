module CategoryTheory.Instances.EndoRelationAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Instances.EndoRelationAsEndoRelation

%access public
%default total

------------------------------------------------------------

instance Classic0CategoryFullClass EndoRelationRecord (~>) 
  where

    getIdentity0 _ _ = MkEndoRelationMorphism 
        id 
        (\_,_ => id)

    getMultiply0 _ _ _ (mor12 & mor23) = MkEndoRelationMorphism
        ((recMap mor23) . (recMap mor12))
        (\_,_ => (recFunctor mor23 _ _) . (recFunctor mor12 _ _))

EndoRelationClassic0CategoryFull' : Classic0CategoryFullClass EndoRelationRecord (~>)
EndoRelationClassic0CategoryFull' = %instance

EndoRelationClassic0CategoryFull : Classic0CategoryFullRecord
EndoRelationClassic0CategoryFull = mkClassic0Category @{EndoRelationClassic0CategoryFull'}

instance Classic0CategoryShortClass EndoRelationRecord 
  where {}

EndoRelationClassic0CategoryShort' : Classic0CategoryShortClass EndoRelationRecord
EndoRelationClassic0CategoryShort' = %instance

EndoRelationClassic0CategoryShort : Classic0CategoryShortRecord
EndoRelationClassic0CategoryShort = mkClassic0Category @{EndoRelationClassic0CategoryShort'}

