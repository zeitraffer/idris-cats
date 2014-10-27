module CategoryTheory.Instances.PlainFunctorAsGraph

------------------------------------------------------------

import CategoryTheory.Classes.Graph

%access public
%default total

------------------------------------------------------------

PlainFunctor : Type
PlainFunctor = Type -> Type

instance GraphClass PlainFunctor
  where
    (|~>|) source target = 
      (arg: Type) -> (source arg) -> (target arg)

