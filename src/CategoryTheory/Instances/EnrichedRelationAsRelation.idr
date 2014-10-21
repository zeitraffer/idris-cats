module CategoryTheory.Instances.EnrichedRelationAsRelation

------------------------------------------------------------

import CategoryTheory.Classes.Relation
import CategoryTheory.Classes.EnrichedRelation

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
      (map: |rSource| -> |rTarget| ) ->
      IsEnrichedFunctor0 rOver rSource rTarget map ->
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

EnrichedRelationRelation' : (RelationClass over) => RelationClass (EnrichedRelationRecord over)
EnrichedRelationRelation' {over} = %instance

EnrichedRelationRelation : RelationRecord -> RelationRecord
EnrichedRelationRelation rOver = mkRelation @{EnrichedRelationRelation' @{recInstance rOver}}

