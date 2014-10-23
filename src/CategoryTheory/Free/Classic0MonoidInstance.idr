module CategoryTheory.Free.Classic0MonoidInstance

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Free.Classic0MonoidType

%access public
%default total

------------------------------------------------------------

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
