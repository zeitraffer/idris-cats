module CategoryTheory.Concrete.TypeAsRelation

import CategoryTheory.Concrete.Relation

%access public
%default total

------------------------------------------------------------

record TypeMorphism : Relation_Arrow Type where
  MkTypeMor : 
    {source, target: Type} ->
    (recMor: source -> target) ->
    TypeMorphism source target

instance Apply0Class (TypeMorphism source target) source target where
  ($) = recMor

instance RelationClass Type where
  (~>) = TypeMorphism

TypeRelation : RelationRecord
TypeRelation = mkRelation {ob = Type}

