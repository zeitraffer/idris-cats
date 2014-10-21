module CategoryTheory.Instances.RelationAsEnrichedRelation

------------------------------------------------------------

import CategoryTheory.Classes.Relation
import CategoryTheory.Classes.EnrichedRelation
import CategoryTheory.Instances.RelationAsRelation
import CategoryTheory.Instances.RelationMorphismAsRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedRelationClass RelationRecord RelationRecord where
  (:>) = RelationMorphismRelation

RelationEnrichedRelation' : EnrichedRelationClass RelationRecord RelationRecord
RelationEnrichedRelation' = %instance

RelationEnrichedRelation : EnrichedRelationRecord RelationRecord
RelationEnrichedRelation = mkEnrichedRelation @{RelationEnrichedRelation'}

