module CategoryTheory.Instances.GraphAsGraph

------------------------------------------------------------

import CategoryTheory.Classes.Graph

%access public
%default total

------------------------------------------------------------

IsFunctor0' : 
  (GraphClass source, GraphClass target) => 
  (source -> target) -> Type
IsFunctor0' {source} f = (x, y: source) -> (x |~>| y) -> (f x |~>| f y)

IsFunctor0 : 
  (rSource, rTarget: GraphRecord) -> 
  ( |rSource| -> |rTarget| ) -> Type
IsFunctor0 rSource rTarget = IsFunctor0' @{recInstance rSource} @{recInstance rTarget}

data GraphMorphism : Graph_Arrow GraphRecord 
  where
    MkGraphMorphism : 
      {rSource, rTarget: GraphRecord} ->
      (map: |rSource| -> |rTarget|) ->
      IsFunctor0 rSource rTarget map ->
      GraphMorphism rSource rTarget

instance GraphClass GraphRecord 
  where
    (|~>|) = GraphMorphism

GraphGraph' : GraphClass GraphRecord
GraphGraph' = %instance

GraphGraph : GraphRecord
GraphGraph = mkGraph @{GraphGraph'}

recMap : 
  {rSource, rTarget: GraphRecord} ->
  rSource |~>| rTarget ->
  |rSource| -> |rTarget|
recMap (MkGraphMorphism map functor) = map

recFunctor : 
  {rSource, rTarget: GraphRecord} ->
  (mor: rSource |~>| rTarget) ->
  IsFunctor0 rSource rTarget (recMap mor) 
recFunctor (MkGraphMorphism map functor) = functor

instance Apply0Class (GraphMorphism rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

-- TODO: promote ($~) to type class method?
($:) : {rSource, rTarget: GraphRecord} ->
       {x, y: |rSource| } ->
       (f: GraphMorphism rSource rTarget) ->
       (Hom rSource x y) -> 
       (Hom rTarget (f $ x) (f $ y))
($:) {x} {y} f = recFunctor f x y

