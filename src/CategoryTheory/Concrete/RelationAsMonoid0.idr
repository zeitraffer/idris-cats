module CategoryTheory.Concrete.RelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsMonoid0

data UnitMorphism : Relation_Arrow unit where
  MkUnitMorphism : UnitMorphism () ()

instance RelationClass unit where
  (~>) = UnitMorphism

UnitRelation : Monoid0_Unit RelationRecord
UnitRelation _ = MkRelation unit %instance

data ProductMorphism : 
    (rLeft, rRight: RelationRecord) ->
    Relation_Arrow ( |rLeft| # |rRight| )
  where
    MkProductMorphism : 
      (RelationClass left, RelationClass right) =>
      {leftSource, leftTarget: left } ->
      {rightSource, rightTarget: right } ->
      (leftSource ~> leftTarget) ->
      (rightSource ~> rightTarget) ->
      ProductMorphism (MkRelation left %instance)
                      (MkRelation right %instance)
                      (leftSource & rightSource)
                      (leftTarget & rightTarget)

instance (RelationClass left, RelationClass right) => 
         RelationClass (left # right) 
  where
    (~>) = ProductMorphism (MkRelation left %instance) 
                           (MkRelation right %instance)

ProductRelation' : (RelationClass left, RelationClass right) => RelationRecord
ProductRelation' {left} {right} = MkRelation (left # right) %instance

ProductRelation : Monoid0_Product RelationRecord
ProductRelation (rLeft, rRight) = ProductRelation' @{recInstance rLeft} @{recInstance rRight}

instance Monoid0Class RelationRecord where
  getUnit0 = UnitRelation 
  getProduct0 = ProductRelation 

RelationMonoid0 : Monoid0Record
RelationMonoid0 = MkMonoid0 RelationRecord %instance

