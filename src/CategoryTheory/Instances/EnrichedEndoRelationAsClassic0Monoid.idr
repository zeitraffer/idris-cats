module CategoryTheory.Instances.EnrichedEndoRelationAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Classes.EnrichedEndoRelation
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

data UnitOver : Type -> Type where
  MkUnitOver : (t: Type) -> UnitOver t

instance 
    (Classic0MonoidClass over) => 
    EnrichedEndoRelationClass over (UnitOver over) 
  where
    (:>) _ _ = unit

UnitEnrichedEndoRelation' : (Classic0MonoidClass over) => EnrichedEndoRelationClass over (UnitOver over)
UnitEnrichedEndoRelation' {over} = %instance

UnitEnrichedEndoRelation : (rOver: Classic0MonoidRecord) -> EnrichedEndoRelationRecord |rOver|
UnitEnrichedEndoRelation rOver = mkEnrichedEndoRelation @{UnitEnrichedEndoRelation' @{recInstance rOver}}

instance 
    (Classic0MonoidClass over, EnrichedEndoRelationClass over left, EnrichedEndoRelationClass over right) => 
    EnrichedEndoRelationClass over (left # right) 
  where
    (:>) (leftSource & rightSource) (leftTarget & rightTarget) =     
      (leftSource :> leftTarget) # (rightSource :> rightTarget)

ProductEnrichedEndoRelation' : 
  (Classic0MonoidClass over, EnrichedEndoRelationClass over left, EnrichedEndoRelationClass over right) => 
  EnrichedEndoRelationClass over (left # right)
ProductEnrichedEndoRelation' {left} {right} = %instance

ProductEnrichedEndoRelation : 
  (rOver: Classic0MonoidRecord) -> 
  Classic0Monoid_Product (EnrichedEndoRelationRecord |rOver| )
ProductEnrichedEndoRelation rOver (rLeft, rRight) =
  mkEnrichedEndoRelation @{ 
    ProductEnrichedEndoRelation' @{recInstance rOver} 
                             @{recInstance rLeft} 
                             @{recInstance rRight}}

instance 
    (Classic0MonoidClass over) => 
    Classic0MonoidClass (EnrichedEndoRelationRecord over)
  where
    getUnit0 _ = 
      mkEnrichedEndoRelation @{UnitEnrichedEndoRelation'}
    getProduct0 (rLeft, rRight) = 
      mkEnrichedEndoRelation @{ProductEnrichedEndoRelation' @{%instance} 
                                                    @{recInstance rLeft} 
                                                    @{recInstance rRight}}

EnrichedEndoRelationClassic0Monoid' : (Classic0MonoidClass over) => Classic0MonoidClass (EnrichedEndoRelationRecord over)
EnrichedEndoRelationClassic0Monoid' {over} = %instance

EnrichedEndoRelationClassic0Monoid : Classic0MonoidRecord -> Classic0MonoidRecord
EnrichedEndoRelationClassic0Monoid mOver = mkClassic0Monoid @{EnrichedEndoRelationClassic0Monoid' @{recInstance mOver}}

