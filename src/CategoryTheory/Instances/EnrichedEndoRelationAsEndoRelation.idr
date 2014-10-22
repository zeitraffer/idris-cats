module CategoryTheory.Instances.EnrichedEndoRelationAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation
import CategoryTheory.Classes.EnrichedEndoRelation

%access public
%default total

------------------------------------------------------------

IsEnrichedFunctor0' : 
  ( EndoRelationClass over, 
    EnrichedEndoRelationClass over source, 
    EnrichedEndoRelationClass over target ) =>
  (source -> target) -> Type
IsEnrichedFunctor0' {source} f =
    (x, y: source) ->
    (x :> y) ~> (f x :> f y)

IsEnrichedFunctor0 : 
  (rOver: EndoRelationRecord) ->
  (rSource, rTarget: EnrichedEndoRelationRecord |rOver|) ->
  ( |rSource| -> |rTarget| ) -> Type
IsEnrichedFunctor0 rOver rSource rTarget = 
    IsEnrichedFunctor0' @{recInstance rOver} @{recInstance rSource} @{recInstance rTarget}

data EnrichedEndoRelationMorphism : 
    (rOver: EndoRelationRecord) -> 
    EndoRelation_Arrow (EnrichedEndoRelationRecord |rOver| ) 
  where
    MkEnrichedEndoRelationMorphism : 
      {rOver: EndoRelationRecord} ->
      {rSource, rTarget: EnrichedEndoRelationRecord |rOver|} ->
      (map: |rSource| -> |rTarget| ) ->
      IsEnrichedFunctor0 rOver rSource rTarget map ->
      EnrichedEndoRelationMorphism rOver rSource rTarget

recMap : 
  {rOver: EndoRelationRecord} ->
  {rSource, rTarget: EnrichedEndoRelationRecord |rOver|} ->
  EnrichedEndoRelationMorphism rOver rSource rTarget ->
  |rSource| -> |rTarget|
recMap (MkEnrichedEndoRelationMorphism map functor) = map

recFunctor : 
  {rOver: EndoRelationRecord} ->
  {rSource, rTarget: EnrichedEndoRelationRecord |rOver|} ->
  (map: EnrichedEndoRelationMorphism rOver rSource rTarget) ->
  IsEnrichedFunctor0 rOver rSource rTarget (recMap map)
recFunctor (MkEnrichedEndoRelationMorphism map functor) = functor

instance Apply0Class (EnrichedEndoRelationMorphism rOver rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

instance (EndoRelationClass over) => 
    EndoRelationClass (EnrichedEndoRelationRecord over) 
  where
    (~>) = EnrichedEndoRelationMorphism (mkEndoRelation {ob = over})

EnrichedEndoRelationEndoRelation' : 
  (EndoRelationClass over) => EndoRelationClass (EnrichedEndoRelationRecord over)
EnrichedEndoRelationEndoRelation' {over} = %instance

EnrichedEndoRelationEndoRelation : EndoRelationRecord -> EndoRelationRecord
EnrichedEndoRelationEndoRelation rOver = mkEndoRelation @{EnrichedEndoRelationEndoRelation' @{recInstance rOver}}

