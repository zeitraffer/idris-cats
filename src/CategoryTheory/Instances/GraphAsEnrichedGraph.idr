module CategoryTheory.Instances.GraphAsEnrichedGraph

------------------------------------------------------------

import CategoryTheory.Classes.Graph
import CategoryTheory.Classes.EnrichedGraph
import CategoryTheory.Instances.GraphAsGraph
import CategoryTheory.Instances.GraphMorphismAsGraph

%access public
%default total

------------------------------------------------------------

instance EnrichedGraphClass GraphRecord GraphRecord 
  where
    (~>) = GraphMorphismGraph

GraphEnrichedGraph' : EnrichedGraphClass GraphRecord GraphRecord
GraphEnrichedGraph' = %instance

GraphEnrichedGraph : EnrichedGraphRecord GraphRecord
GraphEnrichedGraph = mkEnrichedGraph @{GraphEnrichedGraph'}

