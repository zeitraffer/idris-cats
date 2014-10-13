module CategoryTheory.Concrete.RichRelationAsRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.RichRelation

data 
  RichRelationMorphism : 
    (rOver: RelationRecord) -> 
    Relation_Arrow (RichRelationRecord |rOver| ) 
  where
    MkRichRelationMorphism : 
      ( RelationClass over, 
        RichRelationClass over source, RichRelationClass over target ) =>
      (recMap: source -> target) ->
      (recCongr: (x, y: source) ->
                 (x :> y) ~> (recMap x :> recMap y)) ->
      RichRelationMorphism (MkRelation over %instance)
                           (MkRichRelation source %instance) 
                           (MkRichRelation target %instance)

recMap : RichRelationMorphism rOver rSource rTarget ->
         |rSource| -> |rTarget|
recMap (MkRichRelationMorphism map congr) = map

recCongr : (f: RichRelationMorphism rOver rSource rTarget) ->
           (x, y: |rSource| ) ->
           Hom rOver (RichHom rSource x y)
                     (RichHom rTarget (recMap f x) (recMap f y))
recCongr (MkRichRelationMorphism map congr) = congr

instance Apply0Class (RichRelationMorphism rOver rSource rTarget) 
                     ( |rSource| ) 
                     ( |rTarget| ) 
  where
    ($) = recMap

instance (RelationClass over) => 
         RelationClass (RichRelationRecord over) 
  where
    (~>) = RichRelationMorphism (MkRelation over %instance)

RichRelationRelation' : (RelationClass over) => RelationRecord
RichRelationRelation' {over} = MkRelation (RichRelationRecord over) %instance

RichRelationRelation : RelationRecord -> RelationRecord
RichRelationRelation rOver = RichRelationRelation' @{recInstance rOver}

