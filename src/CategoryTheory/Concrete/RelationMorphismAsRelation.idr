module CategoryTheory.Concrete.RelationMorphismAsRelation

import CategoryTheory.Concrete.RelationAsRelation

instance RelationClass (RelationMorphism rSource rTarget) where 
  (~>) {rSource} {rTarget} mSource mTarget =
    (o: |rSource| ) ->
    Hom rTarget (mSource $ o) (mTarget $ o)

RelationMorphismRelation : RelationRecord ->> RelationRecord
RelationMorphismRelation rSource rTarget = 
  mkRelation {ob = RelationMorphism rSource rTarget}
