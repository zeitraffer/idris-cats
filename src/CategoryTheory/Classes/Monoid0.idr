module CategoryTheory.Classes.Monoid0

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

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

data Monoid0Record : Type where
  MkMonoid0 : 
    (carrier: Type) -> 
    Monoid0Class carrier -> 
    Monoid0Record

recCarrier : Monoid0Record -> Type
recCarrier (MkMonoid0 carrier inst) = carrier

recInstance : (rec: Monoid0Record) -> Monoid0Class (recCarrier rec)
recInstance (MkMonoid0 carrier inst) = inst

mkMonoid0 : (Monoid0Class carrier) => Monoid0Record
mkMonoid0 {carrier} = MkMonoid0 carrier %instance

instance ObClass Monoid0Record where
  Ob = recCarrier    

