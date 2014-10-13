module CategoryTheory.Concrete.RichRelationAsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.RichRelation
import CategoryTheory.Concrete.TypeAsMonoid0

data UnitOver : Type -> Type where
  MkUnitOver : (t: Type) -> UnitOver t

UnitRichMorphism : 
    (Monoid0Class over) => 
    (UnitOver over) ->> over
UnitRichMorphism _ _ = 
    unit

instance (Monoid0Class over) => RichRelationClass over (UnitOver over) where
  (:>) = UnitRichMorphism

UnitRichRelation : (Monoid0Class over) => Monoid0_Unit (RichRelationRecord over)
UnitRichRelation {over} _ = MkRichRelation (UnitOver over) UnitRichMorphism

{-

ProductRichMorphism : 
    (Monoid0Class over, RichRelationClass over left, RichRelationClass over right) => 
    (left # right) ->> over
ProductRichMorphism (leftSource , rightSource) (leftTarget , rightTarget) =     
    (leftSource :> leftTarget) # (rightSource :> rightTarget)

ProductRichRelation : (Monoid0Class over) => Monoid0_Product (RichRelationRecord over)
ProductRichRelation (left, right) = MkRichRelation ( |left| # |right| ) ProductRichMorphism

------------------------------------------

instance RelationClass (left, right) where
  (~>) = ProductMorphism

RelationMonoid0 : Monoid0Record
RelationMonoid0 = MkMonoid0 RelationRecord (UnitRelation, ProductRelation)

instance Monoid0Class RelationRecord where
  getMonoid0 = recIsMonoid RelationMonoid0

-}
