module CategoryTheory.Instances.RelationAsMonoid0

------------------------------------------------------------

import CategoryTheory.Classes.Monoid0
import CategoryTheory.Classes.Relation
import CategoryTheory.Instances.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

data UnitMorphism : Relation_Arrow unit where
  MkUnitMorphism : UnitMorphism () ()

instance RelationClass unit where
  (~>) = UnitMorphism

UnitRelation' : RelationClass unit
UnitRelation' = %instance

UnitRelation : RelationRecord
UnitRelation = mkRelation @{UnitRelation'}

IsProductMorphism' :
  (RelationClass left, RelationClass right) =>
  Relation_Arrow (left # right)
IsProductMorphism' (leftSource & rightSource) (leftTarget & rightTarget) =
  (leftSource ~> leftTarget) # (rightSource ~> rightTarget)

IsProductMorphism :
  (rLeft, rRight: RelationRecord) -> Relation_Arrow ( |rLeft| # |rRight| )
IsProductMorphism rLeft rRight = 
  IsProductMorphism' @{recInstance rLeft} @{recInstance rRight}

data 
  ProductMorphism : 
    (rLeft, rRight: RelationRecord) -> Relation_Arrow ( |rLeft| # |rRight| )
  where
    MkProductMorphism : 
      {rLeft, rRight: RelationRecord} -> 
      {source, target: |rLeft| # |rRight| } ->
      IsProductMorphism rLeft rRight source target ->
      ProductMorphism rLeft rRight source target                      

recMor : 
  {rLeft, rRight: RelationRecord} -> 
  {source, target: |rLeft| # |rRight| } ->
  ProductMorphism rLeft rRight source target ->
  IsProductMorphism rLeft rRight source target
recMor (MkProductMorphism mor) = mor

instance (RelationClass left, RelationClass right) => 
         RelationClass (left # right) 
  where
    (~>) = ProductMorphism (mkRelation {ob = left}) (mkRelation {ob = right})

ProductRelation' : 
  (RelationClass left, RelationClass right) => RelationClass (left # right)
ProductRelation' {left} {right} = %instance

ProductRelation : Monoid0_Product RelationRecord
ProductRelation (rLeft, rRight) = 
  mkRelation @{ProductRelation' @{recInstance rLeft} @{recInstance rRight}}

instance Monoid0Class RelationRecord where
  getUnit0 _ = UnitRelation 
  getProduct0 = ProductRelation

RelationMonoid0' : Monoid0Class RelationRecord
RelationMonoid0' = %instance

RelationMonoid0 : Monoid0Record
RelationMonoid0 = mkMonoid0 @{RelationMonoid0'}

