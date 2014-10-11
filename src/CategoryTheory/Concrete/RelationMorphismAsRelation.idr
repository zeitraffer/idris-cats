module CategoryTheory.Concrete.RelationMorphismAsRelation

import CategoryTheory.Concrete.RelationAsRelation

RelationMorphismMorphism : 
  {rSource, rTarget: RelationRecord} -> 
  (rSource ~> rTarget) ->>
  Type
RelationMorphismMorphism {rSource} {rTarget} mSource mTarget =
  (o: |rSource| ) ->
  recIsRel rTarget (mSource $ o) (mTarget $ o)

instance RelationClass (RelationMorphism rSource rTarget) where 
  (~>) = RelationMorphismMorphism

RelationMorphismRelation : RelationRecord ->> RelationRecord
RelationMorphismRelation rSource rTarget = 
  MkRelation (RelationMorphism rSource rTarget) RelationMorphismMorphism
