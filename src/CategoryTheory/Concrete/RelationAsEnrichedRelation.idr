module CategoryTheory.Concrete.RelationAsEnrichedRelation

------------------------------------------------------------

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.RelationAsRelation
import CategoryTheory.Concrete.RelationMorphismAsRelation
import CategoryTheory.Concrete.EnrichedRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedRelationClass RelationRecord RelationRecord where
  (:>) = RelationMorphismRelation

RelationEnrichedRelation : EnrichedRelationRecord RelationRecord
RelationEnrichedRelation = mkEnrichedRelation {ob = RelationRecord}

