module CategoryTheory.Free.Unbiased0MonoidType

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Classic0Monoid

%access public
%default total

------------------------------------------------------------

-- yes, it's `List`
using (carrier: Type) 
  data FreeUnbiased0MonoidType : Type -> Type 
    where
      Nil : FreeUnbiased0MonoidType carrier
      (::) : carrier -> FreeUnbiased0MonoidType carrier -> FreeUnbiased0MonoidType carrier

-- TODO PlainMonad

