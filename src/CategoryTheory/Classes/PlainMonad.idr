module CategoryTheory.Classes.PlainMonad

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Classes.Graph
import CategoryTheory.Instances.PlainFunctorAsGraph
import CategoryTheory.Instances.PlainFunctorAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

-- TODO equivalence to 'monoid in category of endofunctors'

PlainMonad_Unit : PlainFunctor -> Type
PlainMonad_Unit f = unit |~>| f    

PlainMonad_Multiply : PlainFunctor -> Type
PlainMonad_Multiply f = (f # f) |~>| f    

class PlainMonadClass (func: PlainFunctor) where
  getMonadUnit :  PlainMonad_Unit func
  getMonadMultiply : PlainMonad_Multiply func

data PlainMonadRecord : Type where
  MkPlainMonad :
    (func: PlainFunctor) ->
    PlainMonadClass func ->
    PlainMonadRecord

recFunctor : PlainMonadRecord -> PlainFunctor
recFunctor (MkPlainMonad func inst) = func

recInstance : (rec: PlainMonadRecord) -> PlainMonadClass (recFunctor rec)
recInstance (MkPlainMonad func inst) = inst

