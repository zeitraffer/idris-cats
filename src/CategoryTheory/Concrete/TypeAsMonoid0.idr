module CategoryTheory.Concrete.TypeAsMonoid0

import CategoryTheory.Concrete.Monoid0

UnitType : Monoid0_Unit Type 
UnitType = ()

ProductType : Monoid0_Product Type
ProductType left right = (left, right)

instance Monoid0Class Type where
  getUnit = UnitType
  getProduct = ProductType

TypeMonoid0 : Monoid0
TypeMonoid0 = MkMonoid0 Type (UnitType, ProductType)  

(&) : left -> right -> (left # right)
l & r = (l, r)

