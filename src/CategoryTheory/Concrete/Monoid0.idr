module CategoryTheory.Concrete.Monoid0

import CategoryTheory.Common

Monoid0_Unit : Type -> Type
Monoid0_Unit carrier = () -> carrier

Monoid0_Product : Type -> Type
Monoid0_Product carrier = (carrier, carrier) -> carrier

IsMonoid0 : Type -> Type
IsMonoid0 carrier = 
  ( Monoid0_Unit carrier,
    Monoid0_Product carrier )

recUnit : IsMonoid0 carrier -> Monoid0_Unit carrier
recUnit (u, p) = u

recProduct : IsMonoid0 carrier -> Monoid0_Product carrier
recProduct (u, p) = p

record Monoid0 : Type where
  MkMonoid0 : 
    (recCarrier: Type) -> 
    (recIsMonoid: IsMonoid0 recCarrier) -> 
    Monoid0

instance ObClass Monoid0 where
  Ob = recCarrier    

class Monoid0Class (carrier : Type) where
  getMonoid0 : IsMonoid0 carrier

getUnit0 : (Monoid0Class carrier) => Monoid0_Unit carrier 
getUnit0 = recUnit getMonoid0

getProduct0 : (Monoid0Class carrier) => Monoid0_Product carrier 
getProduct0 = recProduct getMonoid0

unit : (Monoid0Class carrier) => carrier
unit = getUnit0 ()

(#) : (Monoid0Class carrier) => carrier -> carrier -> carrier
left # right = getProduct0 (left, right)

