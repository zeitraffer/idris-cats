module CategoryTheory.Concrete.RelationAsCategory0

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.RelationAsRelation

%access public
%default total

------------------------------------------------------------

instance 
    Category0Class RelationRecord (~>) 
  where

    getIdentity0 _ _ = MkRelationMorphism 
        id 
        (\_,_ => id)

    getMultiply0 _ _ _ (mor12 & mor23) = MkRelationMorphism
        ((recMap mor23) . (recMap mor12))
        (\_,_ => (recFunctor mor23 _ _) . (recFunctor mor12 _ _))

RelationCategory0 : Category0Record
RelationCategory0 = mkCategory0 {ob = RelationRecord}

