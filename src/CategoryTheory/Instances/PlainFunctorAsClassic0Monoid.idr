module CategoryTheory.Instances.PlainFunctorAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Instances.PlainFunctorAsGraph
import CategoryTheory.Classes.Classic0Monoid

%access public
%default total

------------------------------------------------------------

instance Classic0MonoidClass PlainFunctor 
  where
    getUnit0 none = id
    getProduct0 (second, first) = \arg => second(first(arg))

PlainFunctorClassic0Monoid : Classic0MonoidRecord
PlainFunctorClassic0Monoid = mkClassic0Monoid {carrier = PlainFunctor}

