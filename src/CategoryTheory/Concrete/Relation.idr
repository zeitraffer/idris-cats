module CategoryTheory.Concrete.Relation

import CategoryTheory.Common

Relation_Arrow : Type -> Type
Relation_Arrow obj = obj ->> Type

class RelationClass (obj: Type) where
  (~>) : Relation_Arrow obj

record RelationRecord : Type where
  MkRelation : 
    (recObj: Type) ->
    (recInstance: RelationClass recObj) ->
    RelationRecord

instance ObClass RelationRecord where
  Ob = recObj

