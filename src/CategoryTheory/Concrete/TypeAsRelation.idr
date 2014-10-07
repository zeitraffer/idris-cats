module CategoryTheory.Concrete.TypeAsRelation

import CategoryTheory.Concrete.Relation

record TypeMorphism : Type ->> Type where
  MkTypeMor : 
    {source, target: Type} ->
    (unTypeMor: source -> target) ->
    TypeMorphism source target

instance ApplyClass (TypeMorphism source target) source target where
  (MkTypeMor mor) $ s = mor s

instance RelationClass Type where
  (~>) = TypeMorphism

TypeRelation : Relation
TypeRelation = MkRelation Type TypeMorphism

