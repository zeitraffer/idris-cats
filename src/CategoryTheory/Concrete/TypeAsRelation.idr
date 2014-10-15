module CategoryTheory.Concrete.TypeAsRelation

import CategoryTheory.Concrete.Relation

%access public
%default total

------------------------------------------------------------

data TypeMorphism : Relation_Arrow Type where
  MkTypeMor : 
    {source, target: Type} ->
    (recMor: source -> target) ->
    TypeMorphism source target

recMor : {source, target: Type} -> TypeMorphism source target -> source -> target
recMor (MkTypeMor mor) = mor

instance Apply0Class (TypeMorphism source target) source target where
  ($) = recMor

instance RelationClass Type where
  (~>) = TypeMorphism

TypeRelation : RelationRecord
TypeRelation = mkRelation {ob = Type}

