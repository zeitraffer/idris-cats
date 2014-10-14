module CategoryTheory.Concrete.RichRelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.RichRelation
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

data UnitOver : Type -> Type where
  MkUnitOver : (t: Type) -> UnitOver t

instance 
    (Monoid0Class over) => 
    RichRelationClass over (UnitOver over) 
  where
    (:>) _ _ = unit

UnitRichRelation' : (Monoid0Class over) => RichRelationRecord over
UnitRichRelation' {over} = mkRichRelation {ob = UnitOver over}

UnitRichRelation : (rOver: Monoid0Record) -> RichRelationRecord |rOver|
UnitRichRelation rOver = UnitRichRelation' @{recInstance rOver}

instance 
    (Monoid0Class over, RichRelationClass over left, RichRelationClass over right) => 
    RichRelationClass over (left # right) 
  where
    (:>) (leftSource & rightSource) (leftTarget & rightTarget) =     
      (leftSource :> leftTarget) # (rightSource :> rightTarget)

ProductRichRelation' : 
  (RichRelationClass over left, RichRelationClass over right, Monoid0Class over) => 
  RichRelationRecord over
ProductRichRelation' {left} {right} = mkRichRelation {ob = left # right}

ProductRichRelation : (rOver: Monoid0Record) -> Monoid0_Product (RichRelationRecord |rOver| )
ProductRichRelation rOver (rLeft, rRight) = 
  ProductRichRelation' @{recInstance rLeft} @{recInstance rRight} @{recInstance rOver}

instance 
    (Monoid0Class over) => 
    Monoid0Class (RichRelationRecord over)
  where
    getUnit0 _ = UnitRichRelation'
    getProduct0 (rLeft, rRight) = ProductRichRelation' @{recInstance rLeft} @{recInstance rRight}

RichRelationMonoid0' : (Monoid0Class over) => Monoid0Record
RichRelationMonoid0' {over} = mkMonoid0 {carrier = RichRelationRecord over}

RichRelationMonoid0 : Monoid0Record -> Monoid0Record
RichRelationMonoid0 mOver = RichRelationMonoid0' @{recInstance mOver}

