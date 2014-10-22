module CategoryTheory.Instances.MappingAsEnrichedEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EnrichedEndoRelation
import CategoryTheory.Instances.MappingAsEndoRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedEndoRelationClass MappingOb MappingOb where
  (:>) source target = MkMappingOb (MappingMorphism source target)

MappingEnrichedEndoRelation' : EnrichedEndoRelationClass MappingOb MappingOb
MappingEnrichedEndoRelation' = %instance

MappingEnrichedEndoRelation : EnrichedEndoRelationRecord MappingOb
MappingEnrichedEndoRelation = mkEnrichedEndoRelation @{MappingEnrichedEndoRelation'}

