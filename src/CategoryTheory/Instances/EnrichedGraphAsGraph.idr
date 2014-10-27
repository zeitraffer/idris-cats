module CategoryTheory.Instances.EnrichedGraphAsGraph

------------------------------------------------------------

import CategoryTheory.Classes.Graph
import CategoryTheory.Classes.EnrichedGraph

%access public
%default total

------------------------------------------------------------

IsEnrichedFunctor0' : 
  ( GraphClass over, 
    EnrichedGraphClass over source, 
    EnrichedGraphClass over target ) =>
  (source -> target) -> Type
IsEnrichedFunctor0' {source} f =
    (x, y: source) ->
    (x ~> y) |~>| (f x ~> f y)

IsEnrichedFunctor0 : 
  (rOver: GraphRecord) ->
  (rSource, rTarget: EnrichedGraphRecord |rOver|) ->
  ( |rSource| -> |rTarget| ) -> Type
IsEnrichedFunctor0 rOver rSource rTarget = 
    IsEnrichedFunctor0' @{recInstance rOver} @{recInstance rSource} @{recInstance rTarget}

data EnrichedGraphMorphism : 
    (rOver: GraphRecord) -> 
    Graph_Arrow (EnrichedGraphRecord |rOver| ) 
  where
    MkEnrichedGraphMorphism : 
      {rOver: GraphRecord} ->
      {rSource, rTarget: EnrichedGraphRecord |rOver|} ->
      (map: |rSource| -> |rTarget| ) ->
      IsEnrichedFunctor0 rOver rSource rTarget map ->
      EnrichedGraphMorphism rOver rSource rTarget

recMap : 
  {rOver: GraphRecord} ->
  {rSource, rTarget: EnrichedGraphRecord |rOver|} ->
  EnrichedGraphMorphism rOver rSource rTarget ->
  |rSource| -> |rTarget|
recMap (MkEnrichedGraphMorphism map functor) = map

recFunctor : 
  {rOver: GraphRecord} ->
  {rSource, rTarget: EnrichedGraphRecord |rOver|} ->
  (map: EnrichedGraphMorphism rOver rSource rTarget) ->
  IsEnrichedFunctor0 rOver rSource rTarget (recMap map)
recFunctor (MkEnrichedGraphMorphism map functor) = functor

instance Apply0Class (EnrichedGraphMorphism rOver rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

instance (GraphClass over) => 
    GraphClass (EnrichedGraphRecord over) 
  where
    (|~>|) = EnrichedGraphMorphism (mkGraph {ob = over})

EnrichedGraphGraph' : 
  (GraphClass over) => GraphClass (EnrichedGraphRecord over)
EnrichedGraphGraph' {over} = %instance

EnrichedGraphGraph : GraphRecord -> GraphRecord
EnrichedGraphGraph rOver = mkGraph @{EnrichedGraphGraph' @{recInstance rOver}}

