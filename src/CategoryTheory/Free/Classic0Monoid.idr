module CategoryTheory.Free.Classic0Monoid

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Classic0Monoid

%access public
%default total

------------------------------------------------------------

using (carrier: Type) 
  data FreeClassic0MonoidType : Type -> Type 
    where
      MkMonoidPrimitive : 
        carrier -> FreeClassic0MonoidType carrier
      MkMonoidUnit : 
        Classic0Monoid_Unit (FreeClassic0MonoidType carrier)
      MkMonoidProduct : 
        Classic0Monoid_Product (FreeClassic0MonoidType carrier)

instance Classic0MonoidClass (FreeClassic0MonoidType carrier) 
  where
    getUnit0 = MkMonoidUnit
    getProduct0 = MkMonoidProduct   

FreeClassic0Monoid' : 
  (carrier: Type) -> 
  Classic0MonoidClass (FreeClassic0MonoidType carrier)
FreeClassic0Monoid' _ = %instance

FreeClassic0Monoid : Type -> Classic0MonoidRecord
FreeClassic0Monoid carrier = mkClassic0Monoid @{FreeClassic0Monoid' carrier}

-- TODO functor, adjunction, monad, comonad
