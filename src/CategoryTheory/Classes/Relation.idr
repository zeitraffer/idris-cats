module CategoryTheory.Classes.Relation

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

Relation_Arrow : Type -> Type
Relation_Arrow ob = ob ->> Type

class RelationClass (ob: Type) where
  (~>) : Relation_Arrow ob

data RelationRecord : Type where
  MkRelation : 
    (ob: Type) ->
    RelationClass ob ->
    RelationRecord

recOb : RelationRecord -> Type
recOb (MkRelation ob inst) = ob

recInstance : (rec: RelationRecord) -> RelationClass (recOb rec)
recInstance (MkRelation ob inst) = inst

mkRelation : (RelationClass ob) => RelationRecord
mkRelation {ob} = MkRelation ob %instance

instance ObClass RelationRecord where
  Ob = recOb

Hom : (relation: RelationRecord) -> Relation_Arrow |relation|
Hom relation = (~>) @{recInstance relation}

