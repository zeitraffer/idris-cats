module CategoryTheory.Concrete.RichRelationAsRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.RichRelation

IsRichRelationMorphism : 
  (RelationClass over) =>
  (rSource, rTarget: RichRelationRecord over) -> 
  ( |rSource| -> |rTarget| ) -> 
  Type
IsRichRelationMorphism rSource rTarget mor = 
  (oSource, oTarget: |rSource| ) ->
  (recIsRel rSource oSource oTarget) ~>
  (recIsRel rTarget (mor oSource) (mor oTarget))

record RichRelationMorphism : RichRelationRecord over ->> Type where
  MkRichRelationMorphism : 
    (RelationClass over) =>
    {rSource, rTarget: RichRelationRecord over} ->
    (recMap: |rSource| -> |rTarget| ) ->
    (recIsRelMor: IsRichRelationMorphism rSource rTarget recMap) ->
    RichRelationMorphism rSource rTarget

instance ApplyClass (RichRelationMorphism rSource rTarget) 
                    (recObj rSource) 
                    (recObj rTarget) 
  where
    ($) = recMap

instance (RelationClass over) => 
         RelationClass (RichRelationRecord over) 
  where
    (~>) = RichRelationMorphism

RichRelationRelation : Type -> RelationRecord
RichRelationRelation over = MkRelation (RichRelationRecord over) RichRelationMorphism

