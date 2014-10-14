module CategoryTheory.Concrete.Relation

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

Relation_Arrow : Type -> Type
Relation_Arrow ob = ob ->> Type

class RelationClass (ob: Type) where
  (~>) : Relation_Arrow ob

record RelationRecord : Type where
  MkRelation : 
    (recOb: Type) ->
    (recInstance: RelationClass recOb) ->
    RelationRecord

mkRelation : (RelationClass ob) => RelationRecord
mkRelation {ob} = MkRelation ob %instance

instance ObClass RelationRecord where
  Ob = recOb

Hom : (relation: RelationRecord) -> Relation_Arrow |relation|
Hom relation = (~>) @{recInstance relation}

