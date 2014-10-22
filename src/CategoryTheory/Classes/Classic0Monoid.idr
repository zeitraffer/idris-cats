module CategoryTheory.Classes.Classic0Monoid

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

Classic0Monoid_Unit : Type -> Type
Classic0Monoid_Unit carrier = () -> carrier

Classic0Monoid_Product : Type -> Type
Classic0Monoid_Product carrier = (carrier, carrier) -> carrier

class Classic0MonoidClass (carrier : Type) 
  where
    getUnit0 : Classic0Monoid_Unit carrier 
    getProduct0 : Classic0Monoid_Product carrier 

unit : (Classic0MonoidClass carrier) => carrier
unit = getUnit0 ()

(#) : (Classic0MonoidClass carrier) => carrier -> carrier -> carrier
left # right = getProduct0 (left, right)

data Classic0MonoidRecord : Type 
  where
    MkClassic0Monoid : 
      (carrier: Type) -> 
      Classic0MonoidClass carrier -> 
      Classic0MonoidRecord

recCarrier : Classic0MonoidRecord -> Type
recCarrier (MkClassic0Monoid carrier inst) = carrier

recInstance : 
  (rec: Classic0MonoidRecord) -> 
  Classic0MonoidClass (recCarrier rec)
recInstance (MkClassic0Monoid carrier inst) = inst

mkClassic0Monoid : (Classic0MonoidClass carrier) => Classic0MonoidRecord
mkClassic0Monoid {carrier} = MkClassic0Monoid carrier %instance

instance ObClass Classic0MonoidRecord 
  where
    Ob = recCarrier    

