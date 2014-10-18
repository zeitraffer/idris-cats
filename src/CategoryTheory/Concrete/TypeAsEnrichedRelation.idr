module CategoryTheory.Concrete.TypeAsEnrichedRelation

------------------------------------------------------------

import CategoryTheory.Concrete.EnrichedRelation
import CategoryTheory.Concrete.TypeAsRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedRelationClass Type Type where
  (:>) = TypeMorphism

TypeEnrichedRelation' : EnrichedRelationClass Type Type
TypeEnrichedRelation' = %instance

TypeEnrichedRelation : EnrichedRelationRecord Type
TypeEnrichedRelation = mkEnrichedRelation @{TypeEnrichedRelation'}

