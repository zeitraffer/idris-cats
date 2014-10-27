module CategoryTheory.Instances.GraphMorphismAsGraph

------------------------------------------------------------

import CategoryTheory.Instances.GraphAsGraph

%access public
%default total

------------------------------------------------------------

GraphMorphism2' : 
  (GraphClass source, GraphClass target) =>
  GraphMorphism (mkGraph {ob = source}) (mkGraph {ob = target}) ->> 
  Type
GraphMorphism2' {source} {target} m1 m2 = 
  (o: source) -> (m1 $ o)|~>|(m2 $ o)

GraphMorphism2 : 
  {rSource, rTarget: GraphRecord} ->
  GraphMorphism rSource rTarget ->> 
  Type
GraphMorphism2 {rSource = MkGraph source sourceInst} 
                  {rTarget = MkGraph target targetInst} 
  = GraphMorphism2' @{sourceInst} @{targetInst}

instance GraphClass (GraphMorphism rSource rTarget) 
  where 
    (|~>|) = GraphMorphism2

GraphMorphismGraph' : 
  (rSource, rTarget: GraphRecord) -> GraphClass (GraphMorphism rSource rTarget)
GraphMorphismGraph' rSource rTarget = %instance

GraphMorphismGraph : GraphRecord ->> GraphRecord
GraphMorphismGraph rSource rTarget = 
  mkGraph @{GraphMorphismGraph' rSource rTarget}

