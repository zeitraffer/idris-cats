module CategoryTheory.Free.Classic0MonoidType

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

