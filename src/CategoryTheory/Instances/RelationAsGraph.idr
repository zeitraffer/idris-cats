module CategoryTheory.Instances.RelationAsGraph

------------------------------------------------------------

import CategoryTheory.Classes.Graph

%access public
%default total

------------------------------------------------------------

data RelationOb = MkRelationOb Type

instance ObClass RelationOb 
  where
    Ob (MkRelationOb type) = type

IsRelationMorphism : Graph_Arrow RelationOb
IsRelationMorphism oSource oTarget = 
  (source: |oSource| ) -> (target: |oTarget| ) -> Type

data RelationMorphism : Graph_Arrow RelationOb 
  where
    MkRelationMorphism : 
      {source, target: RelationOb} ->
      IsRelationMorphism source target ->
      RelationMorphism source target

recMor : 
  {source, target: RelationOb} -> 
  RelationMorphism source target -> 
  IsRelationMorphism source target
recMor (MkRelationMorphism mor) = mor

instance GraphClass RelationOb 
  where
    (|~>|) = RelationMorphism

RelationGraph' : GraphClass RelationOb
RelationGraph' = %instance

RelationGraph : GraphRecord
RelationGraph = mkGraph @{RelationGraph'}

