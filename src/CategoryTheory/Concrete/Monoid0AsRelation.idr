module CategoryTheory.Concrete.Monoid0AsRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.Monoid0

%access public
%default total

------------------------------------------------------------

data Monoid0Morphism : Relation_Arrow Monoid0Record where
  MkMonoid0Mor : 
    (Monoid0Class source, Monoid0Class target) =>
    (recMor: source -> target) ->
    Monoid0Morphism (mkMonoid0 {carrier = source}) (mkMonoid0 {carrier = target})

recMor : 
  {mSource, mTarget: Monoid0Record} ->
  Monoid0Morphism mSource mTarget ->
  |mSource| -> |mTarget|
recMor (MkMonoid0Mor mor) = mor

instance 
  Apply0Class (Monoid0Morphism mSource mTarget) 
              |mSource| 
              |mTarget|
  where
    ($) = recMor

instance RelationClass Monoid0Record where
  (~>) = Monoid0Morphism

Monoid0Relation : RelationRecord
Monoid0Relation = mkRelation {ob = Monoid0Record}

