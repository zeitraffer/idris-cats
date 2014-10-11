module CategoryTheory.Concrete.RelationAsRelation

import CategoryTheory.Concrete.Relation

IsRelationMorphism : 
  (rSource, rTarget: RelationRecord) -> 
  ( |rSource| -> |rTarget| ) -> 
  Type
IsRelationMorphism rSource rTarget mor = 
  (oSource, oTarget: |rSource| ) ->
  (recIsRel rSource oSource oTarget) ->
  (recIsRel rTarget (mor oSource) (mor oTarget))

record RelationMorphism : RelationRecord ->> Type where
  MkRelationMorphism : 
    {rSource, rTarget: RelationRecord} ->
    (recMap: |rSource| -> |rTarget| ) ->
    (recIsRelMor: IsRelationMorphism rSource rTarget recMap) ->
    RelationMorphism rSource rTarget

instance ApplyClass (RelationMorphism rSource rTarget) 
                    (recObj rSource) 
                    (recObj rTarget) where
  ($) = recMap

instance RelationClass RelationRecord where
  (~>) = RelationMorphism

RelationRelation : RelationRecord
RelationRelation = MkRelation RelationRecord RelationMorphism

