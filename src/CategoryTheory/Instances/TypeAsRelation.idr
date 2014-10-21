module CategoryTheory.Instances.TypeAsRelation

------------------------------------------------------------

import CategoryTheory.Classes.Relation

%access public
%default total

------------------------------------------------------------

data TypeMorphism : Relation_Arrow Type where
  MkTypeMorphism : 
    {source, target: Type} ->
    (source -> target) ->
    TypeMorphism source target

recMor : {source, target: Type} -> TypeMorphism source target -> source -> target
recMor (MkTypeMorphism mor) = mor

instance 
    Apply0Class 
      (TypeMorphism source target) 
      source 
      target 
  where
    ($) = recMor

instance 
    RelationClass 
      Type 
  where
    (~>) = TypeMorphism

TypeRelation' : RelationClass Type
TypeRelation' = %instance

TypeRelation : RelationRecord
TypeRelation = mkRelation @{TypeRelation'}

