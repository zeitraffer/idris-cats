module CategoryTheory.Concrete.RelationAsRelation

import CategoryTheory.Concrete.Relation

IsRelationMorphism : 
  (rSource, rTarget: Relation) -> 
  ( |rSource| -> |rTarget| ) -> 
  Type
IsRelationMorphism rSource rTarget mor = 
  (oSource, oTarget: |rSource| ) ->
  (recIsRel rSource oSource oTarget) ->
  (recIsRel rTarget (mor oSource) (mor oTarget))

record RelationMorphism : Relation ->> Type where
  MkRelationMorphism : 
    {rSource, rTarget: Relation} ->
    (recMap: |rSource| -> |rTarget| ) ->
    (recIsRelMor: IsRelationMorphism rSource rTarget recMap) ->
    RelationMorphism rSource rTarget

instance ApplyClass (RelationMorphism rSource rTarget) 
                    (recObj rSource) 
                    (recObj rTarget) where
  ($) = recMap

instance RelationClass Relation where
  (~>) = RelationMorphism

RelationRelation : Relation
RelationRelation = MkRelation Relation RelationMorphism

