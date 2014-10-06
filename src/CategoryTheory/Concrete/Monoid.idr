module CategoryTheory.Concrete.Module

import CategoryTheory.Common

record Monoid0 : Type where
  MkMonoid : 
    (recCarrier : Type) ->
    (recOne : recCarrier) ->
    (recProduct : recCarrier -> recCarrier -> recCarrier) ->
    Monoid0



