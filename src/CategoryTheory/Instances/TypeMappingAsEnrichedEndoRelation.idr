module CategoryTheory.Instances.TypeMappingAsEnrichedEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EnrichedEndoRelation
import CategoryTheory.Instances.TypeMappingAsEndoRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedEndoRelationClass Type Type where
  (:>) = TypeMapping

TypeEnrichedEndoRelation' : EnrichedEndoRelationClass Type Type
TypeEnrichedEndoRelation' = %instance

TypeEnrichedEndoRelation : EnrichedEndoRelationRecord Type
TypeEnrichedEndoRelation = mkEnrichedEndoRelation @{TypeEnrichedEndoRelation'}

