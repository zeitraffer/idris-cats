module CategoryTheory.Instances.Classic0MonoidAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation
import CategoryTheory.Classes.Classic0Monoid

%access public
%default total

------------------------------------------------------------

data Classic0MonoidMorphism : EndoRelation_Arrow Classic0MonoidRecord 
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

instance EndoRelationClass Classic0MonoidRecord 
  where
    (~>) = Classic0MonoidMorphism

Classic0MonoidEndoRelation' : EndoRelationClass Classic0MonoidRecord
Classic0MonoidEndoRelation' = %instance

Classic0MonoidEndoRelation : EndoRelationRecord
Classic0MonoidEndoRelation = mkEndoRelation @{Classic0MonoidEndoRelation'}

