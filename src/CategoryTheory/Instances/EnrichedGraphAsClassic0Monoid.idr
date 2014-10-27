module CategoryTheory.Instances.EnrichedGraphAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Classes.EnrichedGraph
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

data UnitOver over = MkUnitOver

instance (Classic0MonoidClass over) => 
    EnrichedGraphClass over (UnitOver over) 
  where
    (~>) _ _ = unit

UnitEnrichedGraph' : 
  (Classic0MonoidClass over) => EnrichedGraphClass over (UnitOver over)
UnitEnrichedGraph' {over} = %instance

UnitEnrichedGraph : 
  (rOver: Classic0MonoidRecord) -> EnrichedGraphRecord |rOver|
UnitEnrichedGraph rOver = 
  mkEnrichedGraph @{UnitEnrichedGraph' @{recInstance rOver}}

instance ( Classic0MonoidClass over, 
           EnrichedGraphClass over left, 
           EnrichedGraphClass over right ) => 
    EnrichedGraphClass over (left # right) 
  where
    (~>) (leftSource & rightSource) (leftTarget & rightTarget) =     
      (leftSource ~> leftTarget) # (rightSource ~> rightTarget)

ProductEnrichedGraph' : 
  ( Classic0MonoidClass over, 
    EnrichedGraphClass over left, 
    EnrichedGraphClass over right) => 
  EnrichedGraphClass over (left # right)
ProductEnrichedGraph' {left} {right} = %instance

ProductEnrichedGraph : 
  (rOver: Classic0MonoidRecord) -> 
  Classic0Monoid_Product (EnrichedGraphRecord |rOver| )
ProductEnrichedGraph rOver (rLeft, rRight) =
  mkEnrichedGraph @{ 
    ProductEnrichedGraph' @{recInstance rOver} 
                             @{recInstance rLeft} 
                             @{recInstance rRight}}

instance (Classic0MonoidClass over) => 
    Classic0MonoidClass (EnrichedGraphRecord over)
  where
    getUnit0 _ = mkEnrichedGraph @{UnitEnrichedGraph'}
    getProduct0 (rLeft, rRight) = 
      mkEnrichedGraph @{ProductEnrichedGraph' @{%instance} 
                                                    @{recInstance rLeft} 
                                                    @{recInstance rRight}}

EnrichedGraphClassic0Monoid' : 
  (Classic0MonoidClass over) => 
  Classic0MonoidClass (EnrichedGraphRecord over)
EnrichedGraphClassic0Monoid' {over} = %instance

EnrichedGraphClassic0Monoid : Classic0MonoidRecord -> Classic0MonoidRecord
EnrichedGraphClassic0Monoid mOver = 
  mkClassic0Monoid @{EnrichedGraphClassic0Monoid' @{recInstance mOver}}

