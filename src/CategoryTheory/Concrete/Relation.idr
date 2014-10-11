module CategoryTheory.Concrete.Relation

import CategoryTheory.Common

IsRelation : Type -> Type
IsRelation obj = obj ->> Type

record RelationRecord : Type where
  MkRelation : 
    (recObj: Type) ->
    (recIsRel: IsRelation recObj) ->
    RelationRecord

instance ObClass RelationRecord where
  Ob = recObj

class RelationClass (obj: Type) where
  (~>) : IsRelation obj


