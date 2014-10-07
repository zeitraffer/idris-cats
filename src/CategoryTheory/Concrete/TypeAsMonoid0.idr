module CategoryTheory.Concrete.TypeAsMonoid0

import CategoryTheory.Concrete.Monoid0

data TypeUnit : Monoid0_Unit Type where
  MkTypeUnit : TypeUnit

data TypeProduct : Monoid0_Product Type where
  MkTypeProduct : 
    {left, right: Type} -> 
    (l: left) ->
    (r: right) ->
    TypeProduct left right

instance Monoid0Class Type where
  getMonoid0 = (TypeUnit, TypeProduct)

TypeMonoid0 : Monoid0
TypeMonoid0 = MkMonoid0 Type (TypeUnit, TypeProduct)  

