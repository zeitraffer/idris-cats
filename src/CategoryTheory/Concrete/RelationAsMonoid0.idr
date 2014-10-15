module CategoryTheory.Concrete.RelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

data UnitMorphism : Relation_Arrow unit where
  MkUnitMorphism : UnitMorphism () ()

instance RelationClass unit where
  (~>) = UnitMorphism

UnitRelation : RelationRecord
UnitRelation = mkRelation {ob = unit}

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

instance (RelationClass left, RelationClass right) => 
         RelationClass (left # right) 
  where
    (~>) = ProductMorphism (mkRelation {ob = left}) (mkRelation {ob = right})

ProductRelation' : (RelationClass left, RelationClass right) => RelationRecord
ProductRelation' {left} {right} = mkRelation {ob = left # right}

ProductRelation : Monoid0_Product RelationRecord
ProductRelation (rLeft, rRight) = ProductRelation' @{recInstance rLeft} @{recInstance rRight}

instance Monoid0Class RelationRecord where
  getUnit0 _ = UnitRelation 
  getProduct0 = ProductRelation

RelationMonoid0 : Monoid0Record
RelationMonoid0 = mkMonoid0 {carrier = RelationRecord}

