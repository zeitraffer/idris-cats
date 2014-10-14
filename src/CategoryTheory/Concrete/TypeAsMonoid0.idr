module CategoryTheory.Concrete.TypeAsMonoid0

import CategoryTheory.Concrete.Monoid0

UnitType : Monoid0_Unit Type 
UnitType () = ()

ProductType : Monoid0_Product Type
ProductType (left, right) = (left, right)

instance Monoid0Class Type where
  getUnit0 = UnitType
  getProduct0 = ProductType

TypeMonoid0 : Monoid0Record
TypeMonoid0 = mkMonoid0 {carrier = Type}

(&) : left -> right -> (left # right)
l & r = (l, r)

