module CategoryTheory.Instances.EnrichedRelationAsMonoid0

------------------------------------------------------------

import CategoryTheory.Classes.Monoid0
import CategoryTheory.Classes.EnrichedRelation
import CategoryTheory.Instances.TypeAsMonoid0

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

UnitEnrichedRelation' : (Monoid0Class over) => EnrichedRelationClass over (UnitOver over)
UnitEnrichedRelation' {over} = %instance

UnitEnrichedRelation : (rOver: Monoid0Record) -> EnrichedRelationRecord |rOver|
UnitEnrichedRelation rOver = mkEnrichedRelation @{UnitEnrichedRelation' @{recInstance rOver}}

instance 
    (Monoid0Class over, EnrichedRelationClass over left, EnrichedRelationClass over right) => 
    EnrichedRelationClass over (left # right) 
  where
    (:>) (leftSource & rightSource) (leftTarget & rightTarget) =     
      (leftSource :> leftTarget) # (rightSource :> rightTarget)

ProductEnrichedRelation' : 
  (Monoid0Class over, EnrichedRelationClass over left, EnrichedRelationClass over right) => 
  EnrichedRelationClass over (left # right)
ProductEnrichedRelation' {left} {right} = %instance

ProductEnrichedRelation : 
  (rOver: Monoid0Record) -> 
  Monoid0_Product (EnrichedRelationRecord |rOver| )
ProductEnrichedRelation rOver (rLeft, rRight) =
  mkEnrichedRelation @{ 
    ProductEnrichedRelation' @{recInstance rOver} 
                             @{recInstance rLeft} 
                             @{recInstance rRight}}

instance 
    (Monoid0Class over) => 
    Monoid0Class (EnrichedRelationRecord over)
  where
    getUnit0 _ = 
      mkEnrichedRelation @{UnitEnrichedRelation'}
    getProduct0 (rLeft, rRight) = 
      mkEnrichedRelation @{ProductEnrichedRelation' @{%instance} 
                                                    @{recInstance rLeft} 
                                                    @{recInstance rRight}}

EnrichedRelationMonoid0' : (Monoid0Class over) => Monoid0Class (EnrichedRelationRecord over)
EnrichedRelationMonoid0' {over} = %instance

EnrichedRelationMonoid0 : Monoid0Record -> Monoid0Record
EnrichedRelationMonoid0 mOver = mkMonoid0 @{EnrichedRelationMonoid0' @{recInstance mOver}}

