module CategoryTheory.Concrete.Relation

import CategoryTheory.Common

IsRelation : Type -> Type
IsRelation obj = obj ->> Type

record Relation : Type where
  MkRelation : 
    (recRelObj: Type) ->
    (recIsRel: IsRelation recRelObj) ->
    Relation

class RelationClass (obj: Type) where
  (~>) : IsRelation obj


