module CategoryTheory.Concrete.EnrichedRelationAsRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.EnrichedRelation

%access public
%default total

------------------------------------------------------------

IsEnrichedFunctor0' : 
  (RelationClass over, EnrichedRelationClass over source, EnrichedRelationClass over target) =>
  (source -> target) -> Type
IsEnrichedFunctor0' {source} f =
    (x, y: source) ->
    (x :> y) ~> (f x :> f y)

IsEnrichedFunctor0 : 
  (rOver: RelationRecord) ->
  (rSource, rTarget: EnrichedRelationRecord |rOver|) ->
  ( |rSource| -> |rTarget| ) -> Type
IsEnrichedFunctor0 rOver rSource rTarget = 
    IsEnrichedFunctor0' @{recInstance rOver} @{recInstance rSource} @{recInstance rTarget}

data 
  EnrichedRelationMorphism : 
    (rOver: RelationRecord) -> 
    Relation_Arrow (EnrichedRelationRecord |rOver| ) 
  where
    MkEnrichedRelationMorphism : 
      {rOver: RelationRecord} ->
      {rSource, rTarget: EnrichedRelationRecord |rOver|} ->
      (recMap: |rSource| -> |rTarget| ) ->
      (recFunctor: IsEnrichedFunctor0 rOver rSource rTarget recMap) ->
      EnrichedRelationMorphism rOver rSource rTarget

recMap : 
  {rOver: RelationRecord} ->
  {rSource, rTarget: EnrichedRelationRecord |rOver|} ->
  EnrichedRelationMorphism rOver rSource rTarget ->
  |rSource| -> |rTarget|
recMap (MkEnrichedRelationMorphism map functor) = map

recFunctor : 
  {rOver: RelationRecord} ->
  {rSource, rTarget: EnrichedRelationRecord |rOver|} ->
  (map: EnrichedRelationMorphism rOver rSource rTarget) ->
  IsEnrichedFunctor0 rOver rSource rTarget (recMap map)
recFunctor (MkEnrichedRelationMorphism map functor) = functor

instance Apply0Class (EnrichedRelationMorphism rOver rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

instance 
    (RelationClass over) => 
    RelationClass (EnrichedRelationRecord over) 
  where
    (~>) = EnrichedRelationMorphism (mkRelation {ob = over})

EnrichedRelationRelation' : (RelationClass over) => RelationRecord
EnrichedRelationRelation' {over} = mkRelation {ob = EnrichedRelationRecord over}

EnrichedRelationRelation : RelationRecord -> RelationRecord
EnrichedRelationRelation rOver = EnrichedRelationRelation' @{recInstance rOver}

