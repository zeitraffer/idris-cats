module CategoryTheory.Concrete.TypeAsMonoid0

import CategoryTheory.Concrete.Monoid0

TypeUnit : Monoid0_Unit Type
TypeUnit = ()

TypeProduct : Monoid0_Product Type
TypeProduct left right = (left, right)

instance Monoid0Class Type where
  getMonoid0 = (TypeUnit, TypeProduct)

TypeMonoid0 : Monoid0
TypeMonoid0 = MkMonoid0 Type getMonoid0  

