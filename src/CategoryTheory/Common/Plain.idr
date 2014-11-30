module CategoryTheory.Common.Plain

------------------------------------------------------------

import CategoryTheory.Common.Infix
import CategoryTheory.Common.Core

%access public
%default total

------------------------------------------------------------

PlainFunctor : Type
PlainFunctor = Type -> Type

-- do we need this?
instance Apply0Class PlainFunctor Type Type
  where
    ($) = id

PlainFunctorMorphism : PlainFunctor ->> Type
PlainFunctorMorphism source target = (arg: Type) -> (source arg) -> (target arg)

using (f: PlainFunctor, t: Type)
  data FreeMonadType : PlainFunctor -> PlainFunctor 
    where
      MkZero : t -> FreeMonadType f t
      MkSucc : f (FreeMonadType f t) -> FreeMonadType f t

