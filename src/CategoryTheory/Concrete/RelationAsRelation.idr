module CategoryTheory.Concrete.RelationAsRelation

import CategoryTheory.Concrete.Relation

%access public
%default total

------------------------------------------------------------

data RelationMorphism : Relation_Arrow RelationRecord where
  MkRelationMorphism : 
    (RelationClass source, RelationClass target) =>
    (recMap: source -> target) ->
    (recCongr: (x, y: source) ->
               (x ~> y) -> (recMap x ~> recMap y)) ->
    RelationMorphism (mkRelation {ob = source}) 
                     (mkRelation {ob = target})

instance RelationClass RelationRecord where
  (~>) = RelationMorphism

RelationRelation : RelationRecord
RelationRelation = mkRelation {ob = RelationRecord}

recMap : {rSource, rTarget: RelationRecord} ->
         rSource ~> rTarget ->
         |rSource| -> |rTarget|
recMap (MkRelationMorphism map congr) = map

recCongr : {rSource, rTarget: RelationRecord} ->
           (f: rSource ~> rTarget) ->
           (x, y: |rSource| ) ->
           (Hom rSource x y) -> 
           (Hom rTarget (recMap f x) (recMap f y))
recCongr (MkRelationMorphism map congr) = congr

instance 
  Apply0Class (RelationMorphism rSource rTarget) 
              ( |rSource| ) 
              ( |rTarget| ) 
  where
    ($) = recMap

-- TODO: promote ($~) to type class method?
($~) : {rSource, rTarget: RelationRecord} ->
       {x, y: |rSource| } ->
       (f: RelationMorphism rSource rTarget) ->
       (Hom rSource x y) -> 
       (Hom rTarget (f $ x) (f $ y))
($~) {x} {y} f = recCongr f x y

