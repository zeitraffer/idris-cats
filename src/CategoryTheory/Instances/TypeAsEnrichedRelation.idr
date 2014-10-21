module CategoryTheory.Instances.TypeAsEnrichedRelation

------------------------------------------------------------

import CategoryTheory.Classes.EnrichedRelation
import CategoryTheory.Instances.TypeAsRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedRelationClass Type Type where
  (:>) = TypeMorphism

TypeEnrichedRelation' : EnrichedRelationClass Type Type
TypeEnrichedRelation' = %instance

TypeEnrichedRelation : EnrichedRelationRecord Type
TypeEnrichedRelation = mkEnrichedRelation @{TypeEnrichedRelation'}

