module CategoryTheory.Instances.Monoid0AsRelation

------------------------------------------------------------

import CategoryTheory.Classes.Relation
import CategoryTheory.Classes.Monoid0

%access public
%default total

------------------------------------------------------------

data Monoid0Morphism : Relation_Arrow Monoid0Record where
  MkMonoid0Morphism : 
    {mSource, mTarget: Monoid0Record} ->
    ( |mSource| -> |mTarget| ) ->
    Monoid0Morphism mSource mTarget

recMor : 
  {mSource, mTarget: Monoid0Record} ->
  Monoid0Morphism mSource mTarget ->
  |mSource| -> |mTarget|
recMor (MkMonoid0Morphism mor) = mor

instance 
  Apply0Class (Monoid0Morphism mSource mTarget) 
              |mSource| 
              |mTarget|
  where
    ($) = recMor

instance RelationClass Monoid0Record where
  (~>) = Monoid0Morphism

Monoid0Relation' : RelationClass Monoid0Record
Monoid0Relation' = %instance

Monoid0Relation : RelationRecord
Monoid0Relation = mkRelation @{Monoid0Relation'}

