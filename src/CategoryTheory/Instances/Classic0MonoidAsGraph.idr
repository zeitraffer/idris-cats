module CategoryTheory.Instances.Classic0MonoidAsGraph

------------------------------------------------------------

import CategoryTheory.Classes.Graph
import CategoryTheory.Classes.Classic0Monoid

%access public
%default total

------------------------------------------------------------

data Classic0MonoidMorphism : Graph_Arrow Classic0MonoidRecord 
  where
    MkClassic0MonoidMorphism : 
      {mSource, mTarget: Classic0MonoidRecord} ->
      ( |mSource| -> |mTarget| ) ->
      Classic0MonoidMorphism mSource mTarget

recMor : 
  {mSource, mTarget: Classic0MonoidRecord} ->
  Classic0MonoidMorphism mSource mTarget ->
  |mSource| -> |mTarget|
recMor (MkClassic0MonoidMorphism mor) = mor

instance Apply0Class (Classic0MonoidMorphism mSource mTarget) 
                     |mSource| 
                     |mTarget|
  where
    ($) = recMor

instance GraphClass Classic0MonoidRecord 
  where
    (|~>|) = Classic0MonoidMorphism

Classic0MonoidGraph' : GraphClass Classic0MonoidRecord
Classic0MonoidGraph' = %instance

Classic0MonoidGraph : GraphRecord
Classic0MonoidGraph = mkGraph @{Classic0MonoidGraph'}

