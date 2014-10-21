module CategoryTheory.Instances.RelationAsCategory0

------------------------------------------------------------

import CategoryTheory.Classes.Category0
import CategoryTheory.Instances.RelationAsRelation

%access public
%default total

------------------------------------------------------------

instance Category0FullClass RelationRecord (~>) where

    getIdentity0 _ _ = MkRelationMorphism 
        id 
        (\_,_ => id)

    getMultiply0 _ _ _ (mor12 & mor23) = MkRelationMorphism
        ((recMap mor23) . (recMap mor12))
        (\_,_ => (recFunctor mor23 _ _) . (recFunctor mor12 _ _))

RelationCategory0Full' : Category0FullClass RelationRecord (~>)
RelationCategory0Full' = %instance

RelationCategory0Full : Category0FullRecord
RelationCategory0Full = mkCategory0 @{RelationCategory0Full'}

instance Category0ShortClass RelationRecord where

RelationCategory0Short' : Category0ShortClass RelationRecord
RelationCategory0Short' = %instance

RelationCategory0Short : Category0ShortRecord
RelationCategory0Short = mkCategory0 @{RelationCategory0Short'}

