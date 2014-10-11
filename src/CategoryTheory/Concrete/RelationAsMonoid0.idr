module CategoryTheory.Concrete.RelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsMonoid0

data UnitMorphism : unit ->> Type where
  MkUnitMorphism : UnitMorphism () ()

instance RelationClass unit where
  (~>) = UnitMorphism

UnitRelation : Monoid0_Unit RelationRecord
UnitRelation _ = MkRelation unit UnitMorphism

data ProductMorphism : 
    {left, right: Type} ->
    (left # right) ->> Type 
  where
    MkProductMorphism : 
      (RelationClass left, RelationClass right) =>
      {leftSource, leftTarget: |left| } ->
      {rightSource, rightTarget: |right| } ->
      (leftSource ~> leftTarget) ->
      (rightSource ~> rightTarget) ->
      ProductMorphism (leftSource & rightSource)
                      (leftTarget & rightTarget)

ProductRelation : Monoid0_Product RelationRecord
ProductRelation (left, right) = MkRelation ( |left| # |right| ) ProductMorphism

instance RelationClass (left, right) where
  (~>) = ProductMorphism

RelationMonoid0 : Monoid0Record
RelationMonoid0 = MkMonoid0 RelationRecord (UnitRelation, ProductRelation)

instance Monoid0Class RelationRecord where
  getMonoid0 = recIsMonoid RelationMonoid0

