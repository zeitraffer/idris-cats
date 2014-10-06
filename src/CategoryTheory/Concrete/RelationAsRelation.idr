module CategoryTheory.Concrete.RelationAsRelation

import CategoryTheory.Concrete.Relation

IsRelationMorphism : 
  (rSource, rTarget: Relation) -> 
  ((recRelObj rSource) -> (recRelObj rTarget)) -> 
  Type
IsRelationMorphism rSource rTarget mor = 
  (oSource, oTarget: recRelObj rSource) ->
  (recIsRel rSource oSource oTarget) ->
  (recIsRel rTarget (mor oSource) (mor oTarget))

record RelationMorphism : (rSource, rTarget: Relation) -> Type where
  MkRelationMorphism : 
    {rSource, rTarget: Relation} ->
    (recRelMorMap: (recRelObj rSource) -> (recRelObj rTarget)) ->
    (recIsRelMor: IsRelationMorphism rSource rTarget recRelMorMap) ->
    RelationMorphism rSource rTarget

instance RelationClass Relation where
  (~>) = RelationMorphism

