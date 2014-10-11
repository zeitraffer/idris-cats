module CategoryTheory.Concrete.TypeAsMonoid0

import CategoryTheory.Concrete.Monoid0

UnitType : Monoid0_Unit Type 
UnitType _ = ()

ProductType : Monoid0_Product Type
ProductType (left, right) = (left, right)

TypeMonoid0 : Monoid0Record
TypeMonoid0 = MkMonoid0 Type (UnitType, ProductType)  

instance Monoid0Class Type where
  getMonoid0 = recIsMonoid TypeMonoid0

(&) : left -> right -> (left # right)
l & r = (l, r)

