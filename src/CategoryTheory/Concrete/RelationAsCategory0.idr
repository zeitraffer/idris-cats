module CategoryTheory.Concrete.RelationAsCategory0

------------------------------------------------------------

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.RelationAsRelation

%access public
%default total

------------------------------------------------------------

instance 
    Category0FullClass RelationRecord (~>) 
  where

    getIdentity0 _ _ = MkRelationMorphism 
        id 
        (\_,_ => id)

    getMultiply0 _ _ _ (mor12 & mor23) = MkRelationMorphism
        ((recMap mor23) . (recMap mor12))
        (\_,_ => (recFunctor mor23 _ _) . (recFunctor mor12 _ _))

RelationCategory0' : Category0FullClass RelationRecord (~>)
RelationCategory0' = %instance

RelationCategory0 : Category0FullRecord
RelationCategory0 = mkCategory0 @{RelationCategory0'}

