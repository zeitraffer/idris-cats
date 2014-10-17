module CategoryTheory.Concrete.TypeAsEnrichedRelation

------------------------------------------------------------

import CategoryTheory.Concrete.EnrichedRelation
import CategoryTheory.Concrete.TypeAsRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedRelationClass Type Type where
  (:>) = TypeMorphism

TypeEnrichedRelation : EnrichedRelationRecord Type
TypeEnrichedRelation = mkEnrichedRelation {ob = Type}

