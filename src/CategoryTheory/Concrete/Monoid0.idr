module CategoryTheory.Concrete.Monoid0

import CategoryTheory.Common

Monoid0_Unit : Type -> Type
Monoid0_Unit carrier = () -> carrier

Monoid0_Product : Type -> Type
Monoid0_Product carrier = (carrier, carrier) -> carrier

class Monoid0Class (carrier : Type) where
  getUnit0 : Monoid0_Unit carrier 
  getProduct0 : Monoid0_Product carrier 

unit : (Monoid0Class carrier) => carrier
unit = getUnit0 ()

(#) : (Monoid0Class carrier) => carrier -> carrier -> carrier
left # right = getProduct0 (left, right)

record Monoid0Record : Type where
  MkMonoid0 : 
    (recCarrier: Type) -> 
    (recInstance: Monoid0Class recCarrier) -> 
    Monoid0Record

instance ObClass Monoid0Record where
  Ob = recCarrier    

