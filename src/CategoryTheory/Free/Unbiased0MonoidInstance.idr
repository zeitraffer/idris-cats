module CategoryTheory.Free.Unbiased0MonoidInstance

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Unbiased0Monoid
import CategoryTheory.Free.Unbiased0MonoidType

%access public
%default total

------------------------------------------------------------

instance Unbiased0MonoidClass (FreeUnbiased0MonoidType carrier) 
  where
    mpaste = ?monadMult   

FreeUnbiased0Monoid' : 
  (carrier: Type) -> 
  Unbiased0MonoidClass (FreeUnbiased0MonoidType carrier)
FreeUnbiased0Monoid' _ = %instance

FreeUnbiased0Monoid : Type -> Unbiased0MonoidRecord
FreeUnbiased0Monoid carrier = mkUnbiased0Monoid @{FreeUnbiased0Monoid' carrier}

-- TODO functor, adjunction, monad, comonad
