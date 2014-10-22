module CategoryTheory.Instances.RelationAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation

%access public
%default total

------------------------------------------------------------

data RelationOb = MkRelationOb Type

instance ObClass RelationOb 
  where
    Ob (MkRelationOb type) = type

data RelationMorphism : EndoRelation_Arrow RelationOb 
  where
    MkRelationMorphism : 
      {source, target: RelationOb} ->
      ( |source| -> |target| -> Type) ->
      RelationMorphism source target

recMor : 
  {source, target: RelationOb} -> 
  RelationMorphism source target -> 
  ( |source| -> |target| -> Type)
recMor (MkRelationMorphism mor) = mor

instance EndoRelationClass RelationOb 
  where
    (~>) = RelationMorphism

RelationEndoRelation' : EndoRelationClass RelationOb
RelationEndoRelation' = %instance

RelationEndoRelation : EndoRelationRecord
RelationEndoRelation = mkEndoRelation @{RelationEndoRelation'}

