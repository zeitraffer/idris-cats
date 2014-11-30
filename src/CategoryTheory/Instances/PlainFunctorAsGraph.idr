module CategoryTheory.Instances.PlainFunctorAsGraph

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Graph

%access public
%default total

------------------------------------------------------------

instance GraphClass PlainFunctor
  where
    (|~>|) = PlainFunctorMorphism

