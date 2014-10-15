module CategoryTheory.Concrete.RelationAsRelation

import CategoryTheory.Concrete.Relation

%access public
%default total

------------------------------------------------------------

IsFunctor0' : (RelationClass source, RelationClass target) => (f: source -> target) -> Type
IsFunctor0' {source} f = (x, y: source) -> (x ~> y) -> (f x ~> f y)

IsFunctor0 : (rSource, rTarget: RelationRecord) -> (map: |rSource| -> |rTarget|) -> Type
IsFunctor0 rSource rTarget = IsFunctor0' @{recInstance rSource} @{recInstance rTarget}

data RelationMorphism : Relation_Arrow RelationRecord where
  MkRelationMorphism : 
    {rSource, rTarget: RelationRecord} ->
    (recMap: |rSource| -> |rTarget|) ->
    (recFunctor: IsFunctor0 rSource rTarget recMap) ->
    RelationMorphism rSource rTarget

instance RelationClass RelationRecord where
  (~>) = RelationMorphism

RelationRelation : RelationRecord
RelationRelation = mkRelation {ob = RelationRecord}

recMap : {rSource, rTarget: RelationRecord} ->
         rSource ~> rTarget ->
         |rSource| -> |rTarget|
recMap (MkRelationMorphism map functor) = map

recFunctor : {rSource, rTarget: RelationRecord} ->
             (mor: rSource ~> rTarget) ->
             IsFunctor0 rSource rTarget (recMap mor) 
recFunctor (MkRelationMorphism map functor) = functor

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
($~) {x} {y} f = recFunctor f x y

