module CategoryTheory.Common.Core

------------------------------------------------------------

import CategoryTheory.Common.Infix

%access public
%default total

------------------------------------------------------------

class ObClass (t : Type) 
  where
    Ob : t -> Type

instance ObClass Type 
  where
    Ob x = x

syntax "|" [t] "|" = Ob t

class Apply0Class (mapType : Type) 
                  (source: Type) 
                  (target: Type) 
  where
    ($) : mapType -> source -> target

