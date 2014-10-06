module CategoryTheory.Concrete.RelationMorphismAsRelation

import CategoryTheory.Concrete.RelationAsRelation

RelationMorphismMorphism : 
  {rSource, rTarget: Relation} -> 
  (mSource, mTarget: RelationMorphism rSource rTarget) -> 
  Type
RelationMorphismMorphism {rSource} {rTarget} mSource mTarget =
  (o: recRelObj rSource) ->
  recIsRel rTarget (recRelMorMap mSource o) (recRelMorMap mTarget o)

instance RelationClass (RelationMorphism rSource rTarget) where 
  (~>) = RelationMorphismMorphism

