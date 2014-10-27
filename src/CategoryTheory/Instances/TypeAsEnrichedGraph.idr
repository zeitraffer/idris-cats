module CategoryTheory.Instances.TypeAsEnrichedGraph

------------------------------------------------------------

import CategoryTheory.Classes.EnrichedGraph
import CategoryTheory.Instances.TypeAsGraph

%access public
%default total

------------------------------------------------------------

instance EnrichedGraphClass Type Type 
  where
    (~>) = TypeMorphism

TypeEnrichedGraph' : EnrichedGraphClass Type Type
TypeEnrichedGraph' = %instance

TypeEnrichedGraph : EnrichedGraphRecord Type
TypeEnrichedGraph = mkEnrichedGraph @{TypeEnrichedGraph'}

