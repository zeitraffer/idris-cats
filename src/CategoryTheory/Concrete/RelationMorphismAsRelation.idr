module CategoryTheory.Concrete.RelationMorphismAsRelation

import CategoryTheory.Concrete.RelationAsRelation

RelationMorphismMorphism : 
  {rSource, rTarget: Relation} -> 
  (mSource, mTarget: rSource ~> rTarget) -> 
  Type
RelationMorphismMorphism {rSource} {rTarget} mSource mTarget =
  (o: |rSource| ) ->
  recIsRel rTarget (mSource $ o) (mTarget $ o)

instance RelationClass (RelationMorphism rSource rTarget) where 
  (~>) = RelationMorphismMorphism

RelationMorphismRelation : (rSource, rTarget: Relation) -> Relation
RelationMorphismRelation rSource rTarget = 
  MkRelation (RelationMorphism rSource rTarget) RelationMorphismMorphism
