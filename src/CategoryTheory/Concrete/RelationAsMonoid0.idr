module CategoryTheory.Concrete.RelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsMonoid0

data UnitMorphism : unit ->> Type where
  MkUnitMorphism : UnitMorphism () ()

instance RelationClass UnitType where
  (~>) = UnitMorphism

UnitRelation : Monoid0_Unit Relation
UnitRelation = MkRelation UnitType UnitMorphism

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

instance RelationClass (left, right) where
  (~>) = ProductMorphism

ProductRelation : Monoid0_Product Relation
ProductRelation left right = MkRelation ( |left| # |right| ) ProductMorphism

instance Monoid0Class Relation where
  getUnit = UnitRelation
  getProduct = ProductRelation

RelationMonoid0 : Monoid0
RelationMonoid0 = MkMonoid0 Relation (UnitRelation, ProductRelation)

