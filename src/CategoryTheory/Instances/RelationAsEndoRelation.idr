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

IsRelationMorphism : EndoRelation_Arrow RelationOb
IsRelationMorphism oSource oTarget = 
  (source: |oSource| ) -> (target: |oTarget| ) -> Type

data RelationMorphism : EndoRelation_Arrow RelationOb 
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

instance EndoRelationClass RelationOb 
  where
    (|~>|) = RelationMorphism

RelationEndoRelation' : EndoRelationClass RelationOb
RelationEndoRelation' = %instance

RelationEndoRelation : EndoRelationRecord
RelationEndoRelation = mkEndoRelation @{RelationEndoRelation'}

