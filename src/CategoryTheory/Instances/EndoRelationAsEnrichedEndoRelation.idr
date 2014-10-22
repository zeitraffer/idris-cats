module CategoryTheory.Instances.EndoRelationAsEnrichedEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation
import CategoryTheory.Classes.EnrichedEndoRelation
import CategoryTheory.Instances.EndoRelationAsEndoRelation
import CategoryTheory.Instances.EndoRelationMorphismAsEndoRelation

%access public
%default total

------------------------------------------------------------

instance EnrichedEndoRelationClass EndoRelationRecord EndoRelationRecord 
  where
    (:>) = EndoRelationMorphismEndoRelation

EndoRelationEnrichedEndoRelation' : EnrichedEndoRelationClass EndoRelationRecord EndoRelationRecord
EndoRelationEnrichedEndoRelation' = %instance

EndoRelationEnrichedEndoRelation : EnrichedEndoRelationRecord EndoRelationRecord
EndoRelationEnrichedEndoRelation = mkEnrichedEndoRelation @{EndoRelationEnrichedEndoRelation'}

