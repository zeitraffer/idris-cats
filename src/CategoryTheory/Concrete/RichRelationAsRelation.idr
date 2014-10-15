module CategoryTheory.Concrete.RichRelationAsRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.RichRelation

%access public
%default total

------------------------------------------------------------

IsRichFunctor0' : 
  (RelationClass over, RichRelationClass over source, RichRelationClass over target) =>
  (source -> target) -> Type
IsRichFunctor0' {source} f =
    (x, y: source) ->
    (x :> y) ~> (f x :> f y)

IsRichFunctor0 : 
  (rOver: RelationRecord) ->
  (rSource, rTarget: RichRelationRecord |rOver|) ->
  ( |rSource| -> |rTarget| ) -> Type
IsRichFunctor0 rOver rSource rTarget = 
    IsRichFunctor0' @{recInstance rOver} @{recInstance rSource} @{recInstance rTarget}

data 
  RichRelationMorphism : 
    (rOver: RelationRecord) -> 
    Relation_Arrow (RichRelationRecord |rOver| ) 
  where
    MkRichRelationMorphism : 
      {rOver: RelationRecord} ->
      {rSource, rTarget: RichRelationRecord |rOver|} ->
      (recMap: |rSource| -> |rTarget| ) ->
      (recFunctor: IsRichFunctor0 rOver rSource rTarget recMap) ->
      RichRelationMorphism rOver rSource rTarget

recMap : 
  {rOver: RelationRecord} ->
  {rSource, rTarget: RichRelationRecord |rOver|} ->
  RichRelationMorphism rOver rSource rTarget ->
  |rSource| -> |rTarget|
recMap (MkRichRelationMorphism map functor) = map

recFunctor : 
  {rOver: RelationRecord} ->
  {rSource, rTarget: RichRelationRecord |rOver|} ->
  (map: RichRelationMorphism rOver rSource rTarget) ->
  IsRichFunctor0 rOver rSource rTarget (recMap map)
recFunctor (MkRichRelationMorphism map functor) = functor

instance Apply0Class (RichRelationMorphism rOver rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

instance 
    (RelationClass over) => 
    RelationClass (RichRelationRecord over) 
  where
    (~>) = RichRelationMorphism (mkRelation {ob = over})

RichRelationRelation' : (RelationClass over) => RelationRecord
RichRelationRelation' {over} = mkRelation {ob = RichRelationRecord over}

RichRelationRelation : RelationRecord -> RelationRecord
RichRelationRelation rOver = RichRelationRelation' @{recInstance rOver}

