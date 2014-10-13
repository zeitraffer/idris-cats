module CategoryTheory.Concrete.TypeAsRelation

import CategoryTheory.Concrete.Relation

record TypeMorphism : Relation_Arrow Type where
  MkTypeMor : 
    {source, target: Type} ->
    (recTypeMor: source -> target) ->
    TypeMorphism source target

instance Apply0Class (TypeMorphism source target) source target where
  ($) = recTypeMor

instance RelationClass Type where
  (~>) = TypeMorphism

TypeRelation : RelationRecord
TypeRelation = MkRelation Type %instance

