module CategoryTheory.Concrete.Relation

import CategoryTheory.Common

IsRelation : Type -> Type
IsRelation obj = obj ->> Type

record Relation : Type where
  MkRelation : 
    (recObj: Type) ->
    (recIsRel: IsRelation recObj) ->
    Relation

instance ObClass Relation where
  Ob = recObj

class RelationClass (obj: Type) where
  (~>) : IsRelation obj


