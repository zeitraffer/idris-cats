module CategoryTheory.Classes.Unbiased0Monoid

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

Monoid0_Paste : Type -> Type
Monoid0_Paste carrier = List carrier -> carrier

class Unbiased0MonoidClass (carrier : Type) 
  where
    mpaste : Monoid0_Paste carrier

data Unbiased0MonoidRecord : Type 
  where
    MkUnbiased0Monoid : 
      (carrier: Type) -> 
      Unbiased0MonoidClass carrier -> 
      Unbiased0MonoidRecord

recCarrier : Unbiased0MonoidRecord -> Type
recCarrier (MkUnbiased0Monoid carrier inst) = carrier

recInstance : 
  (rec: Unbiased0MonoidRecord) -> 
  Unbiased0MonoidClass (recCarrier rec)
recInstance (MkUnbiased0Monoid carrier inst) = inst

mkUnbiased0Monoid : (Unbiased0MonoidClass carrier) => Unbiased0MonoidRecord
mkUnbiased0Monoid {carrier} = MkUnbiased0Monoid carrier %instance

instance ObClass Unbiased0MonoidRecord 
  where
    Ob = recCarrier    

