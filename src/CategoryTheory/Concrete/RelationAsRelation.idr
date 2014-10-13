module CategoryTheory.Concrete.RelationAsRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsRelation

data RelationMorphism : RelationRecord ->> Type where
  MkRelationMorphism : 
    (RelationClass source, RelationClass target) =>
    (recMap: source -> target ) ->
    (recCong: (x, y: source) ->
              (x ~> y) ~> (recMap x ~> recMap y)) ->
    RelationMorphism (MkRelation source %instance) 
                     (MkRelation target %instance)

recMap : 
    (RelationClass source, RelationClass target) =>
    RelationMorphism (MkRelation source %instance) 
                     (MkRelation target %instance) ->
    source -> target
recMap (MkRelationMorphism map cong) = map

recCong : 
    (RelationClass source, RelationClass target) =>
    RelationMorphism (MkRelation source %instance) 
                     (MkRelation target %instance) ->
    (x, y: source) ->
    (x ~> y) ~> (recMap x ~> recMap y)
recMap (MkRelationMorphism map cong) = cong


{-

instance 
  Apply0Class (RelationMorphism rSource rTarget) 
              ( |rSource| ) 
              ( |rTarget| ) 
  where
    ($) = recMap

  ($~) : 
    (RelationClass source, RelationClass target) =>
    {x, y: source} -> 
    (fun: RelationMorphism source target) -> 
    (sourceTo fun x y) -> 
    (targetTo fun (recMap fun x) (recMap fun y))
  ($~) {source} {target} {x} {y} (MkRelationMorphism map cong) = 
    cong x y

instance RelationClass RelationRecord where
  rSource ~> rTarget = RelationMorphism |rSource| |rTarget|

RelationRelation : RelationRecord
RelationRelation = MkRelation RelationRecord %instance

-}

