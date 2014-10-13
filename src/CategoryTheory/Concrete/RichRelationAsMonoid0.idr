module CategoryTheory.Concrete.RichRelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.RichRelation
import CategoryTheory.Concrete.TypeAsMonoid0

data UnitOver : Type -> Type where
  MkUnitOver : (t: Type) -> UnitOver t

UnitRichMorphism : (Monoid0Class over) => (UnitOver over) ->> over
UnitRichMorphism _ _ = unit

instance 
    (Monoid0Class over) => 
    RichRelationClass over (UnitOver over) 
  where
    (:>) = UnitRichMorphism

UnitRichRelation : (Monoid0Class over) => Monoid0_Unit (RichRelationRecord over)
UnitRichRelation {over} () = MkRichRelation (UnitOver over) %instance

ProductRichMorphism : 
    (Monoid0Class over, RichRelationClass over left, RichRelationClass over right) => 
    (left # right) ->> over
ProductRichMorphism (leftSource , rightSource) (leftTarget , rightTarget) =     
    (leftSource :> leftTarget) # (rightSource :> rightTarget)

instance 
    (Monoid0Class over, RichRelationClass over left, RichRelationClass over right) => 
    RichRelationClass over (left # right) 
  where
    (:>) = ProductRichMorphism

ProductRichRelation' : 
  ( Monoid0Class over, 
    RichRelationClass over left, RichRelationClass over right ) => 
    RichRelationRecord over
ProductRichRelation' {left} {right} = MkRichRelation (left # right) %instance

ProductRichRelation : (Monoid0Class over) => Monoid0_Product (RichRelationRecord over)
ProductRichRelation (rLeft, rRight) = 
  ProductRichRelation' @{%instance} @{recInstance rLeft} @{recInstance rRight}

instance 
    (Monoid0Class over) => 
    Monoid0Class (RichRelationRecord over)
  where
    getUnit0 = UnitRichRelation
    getProduct0 = ProductRichRelation

RichRelationMonoid0' : (Monoid0Class over) => Monoid0Record
RichRelationMonoid0' {over} = MkMonoid0 (RichRelationRecord over) %instance

RichRelationMonoid0 : Monoid0Record -> Monoid0Record
RichRelationMonoid0 mOver = RichRelationMonoid0' @{recInstance mOver}
