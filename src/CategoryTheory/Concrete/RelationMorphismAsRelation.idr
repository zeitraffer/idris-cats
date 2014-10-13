module CategoryTheory.Concrete.RelationMorphismAsRelation

import CategoryTheory.Concrete.RelationAsRelation

RelationMorphismMorphism : 
  {rSource, rTarget: RelationRecord} -> 
  Relation_Arrow (rSource ~> rTarget) 
RelationMorphismMorphism {rSource} {rTarget} mSource mTarget =
  (o: |rSource| ) ->
  Hom rTarget (mSource $ o) (mTarget $ o)

instance RelationClass (RelationMorphism rSource rTarget) where 
  (~>) = RelationMorphismMorphism

RelationMorphismRelation : RelationRecord ->> RelationRecord
RelationMorphismRelation rSource rTarget = 
  MkRelation (RelationMorphism rSource rTarget) %instance
