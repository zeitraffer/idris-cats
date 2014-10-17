module CategoryTheory.Concrete.EnrichedRelationAsMonoid0

------------------------------------------------------------

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.EnrichedRelation
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

data UnitOver : Type -> Type where
  MkUnitOver : (t: Type) -> UnitOver t

instance 
    (Monoid0Class over) => 
    EnrichedRelationClass over (UnitOver over) 
  where
    (:>) _ _ = unit

UnitEnrichedRelation' : (Monoid0Class over) => EnrichedRelationRecord over
UnitEnrichedRelation' {over} = mkEnrichedRelation {ob = UnitOver over}

UnitEnrichedRelation : (rOver: Monoid0Record) -> EnrichedRelationRecord |rOver|
UnitEnrichedRelation rOver = UnitEnrichedRelation' @{recInstance rOver}

instance 
    (Monoid0Class over, EnrichedRelationClass over left, EnrichedRelationClass over right) => 
    EnrichedRelationClass over (left # right) 
  where
    (:>) (leftSource & rightSource) (leftTarget & rightTarget) =     
      (leftSource :> leftTarget) # (rightSource :> rightTarget)

ProductEnrichedRelation' : 
  (EnrichedRelationClass over left, EnrichedRelationClass over right, Monoid0Class over) => 
  EnrichedRelationRecord over
ProductEnrichedRelation' {left} {right} = mkEnrichedRelation {ob = left # right}

ProductEnrichedRelation : 
  (rOver: Monoid0Record) -> 
  Monoid0_Product (EnrichedRelationRecord |rOver| )
ProductEnrichedRelation rOver (rLeft, rRight) = 
  ProductEnrichedRelation' @{recInstance rLeft} @{recInstance rRight} @{recInstance rOver}

instance 
    (Monoid0Class over) => 
    Monoid0Class (EnrichedRelationRecord over)
  where
    getUnit0 _ = UnitEnrichedRelation'
    getProduct0 (rLeft, rRight) = ProductEnrichedRelation' @{recInstance rLeft} @{recInstance rRight}

EnrichedRelationMonoid0' : (Monoid0Class over) => Monoid0Record
EnrichedRelationMonoid0' {over} = mkMonoid0 {carrier = EnrichedRelationRecord over}

EnrichedRelationMonoid0 : Monoid0Record -> Monoid0Record
EnrichedRelationMonoid0 mOver = EnrichedRelationMonoid0' @{recInstance mOver}

