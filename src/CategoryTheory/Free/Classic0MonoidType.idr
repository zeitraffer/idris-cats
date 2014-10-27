module CategoryTheory.Free.Classic0MonoidType

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Classes.PlainMonad

%access public
%default total

------------------------------------------------------------

-- yes, it's a free monad
using (carrier: Type) 
  data FreeClassic0MonoidType : Type -> Type 
    where
      MkMonoidPrimitive : 
        carrier -> FreeClassic0MonoidType carrier
      MkMonoidUnit : 
        Classic0Monoid_Unit (FreeClassic0MonoidType carrier)
      MkMonoidProduct : 
        Classic0Monoid_Product (FreeClassic0MonoidType carrier)

monadUnit : PlainMonad_Unit FreeClassic0MonoidType
monadUnit _ = MkMonoidPrimitive

%assert_total -- FIXME
monadMult : PlainMonad_Multiply FreeClassic0MonoidType 
monadMult _ (MkMonoidPrimitive free) = free
monadMult _ (MkMonoidUnit ()) = MkMonoidUnit ()
monadMult _ (MkMonoidProduct (left, right)) = 
  MkMonoidProduct ((monadMult _ left), (monadMult _ right))

instance PlainMonadClass FreeClassic0MonoidType where
  getMonadUnit = monadUnit
  getMonadMultiply = monadMult

