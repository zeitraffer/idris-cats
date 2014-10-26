module CategoryTheory.Instances.PlainFunctorAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation

%access public
%default total

------------------------------------------------------------

PlainFunctor : Type
PlainFunctor = Type -> Type

instance EndoRelationClass PlainFunctor
  where
    (|~>|) source target = 
      (arg: Type) -> (source arg) -> (target arg)

