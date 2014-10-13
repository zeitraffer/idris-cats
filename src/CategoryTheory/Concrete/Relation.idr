module CategoryTheory.Concrete.Relation

import CategoryTheory.Common

Relation_Arrow : Type -> Type
Relation_Arrow ob = ob ->> Type

class RelationClass (ob: Type) where
  (~>) : Relation_Arrow ob

record RelationRecord : Type where
  MkRelation : 
    (recOb: Type) ->
    (recInstance: RelationClass recOb) ->
    RelationRecord

instance ObClass RelationRecord where
  Ob = recOb

Hom : (relation: RelationRecord) -> Relation_Arrow |relation|
Hom relation = (~>) @{recInstance relation}

