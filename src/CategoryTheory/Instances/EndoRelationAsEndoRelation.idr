module CategoryTheory.Instances.EndoRelationAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation

%access public
%default total

------------------------------------------------------------

IsFunctor0' : 
  (EndoRelationClass source, EndoRelationClass target) => 
  (source -> target) -> Type
IsFunctor0' {source} f = (x, y: source) -> (x |~>| y) -> (f x |~>| f y)

IsFunctor0 : 
  (rSource, rTarget: EndoRelationRecord) -> 
  ( |rSource| -> |rTarget| ) -> Type
IsFunctor0 rSource rTarget = IsFunctor0' @{recInstance rSource} @{recInstance rTarget}

data EndoRelationMorphism : EndoRelation_Arrow EndoRelationRecord 
  where
    MkEndoRelationMorphism : 
      {rSource, rTarget: EndoRelationRecord} ->
      (map: |rSource| -> |rTarget|) ->
      IsFunctor0 rSource rTarget map ->
      EndoRelationMorphism rSource rTarget

instance EndoRelationClass EndoRelationRecord 
  where
    (|~>|) = EndoRelationMorphism

EndoRelationEndoRelation' : EndoRelationClass EndoRelationRecord
EndoRelationEndoRelation' = %instance

EndoRelationEndoRelation : EndoRelationRecord
EndoRelationEndoRelation = mkEndoRelation @{EndoRelationEndoRelation'}

recMap : 
  {rSource, rTarget: EndoRelationRecord} ->
  rSource |~>| rTarget ->
  |rSource| -> |rTarget|
recMap (MkEndoRelationMorphism map functor) = map

recFunctor : 
  {rSource, rTarget: EndoRelationRecord} ->
  (mor: rSource |~>| rTarget) ->
  IsFunctor0 rSource rTarget (recMap mor) 
recFunctor (MkEndoRelationMorphism map functor) = functor

instance Apply0Class (EndoRelationMorphism rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

-- TODO: promote ($~) to type class method?
($:) : {rSource, rTarget: EndoRelationRecord} ->
       {x, y: |rSource| } ->
       (f: EndoRelationMorphism rSource rTarget) ->
       (Hom rSource x y) -> 
       (Hom rTarget (f $ x) (f $ y))
($:) {x} {y} f = recFunctor f x y

