module CategoryTheory.Concrete.RichRelation

import CategoryTheory.Common

RichRelation_Arrow : Type -> Type -> Type
RichRelation_Arrow over ob = ob ->> over

class RichRelationClass (over: Type) (ob: Type) where
  (:>) : RichRelation_Arrow over ob

record RichRelationRecord : Type -> Type where
  MkRichRelation : 
    {over: Type} ->
    (recOb: Type) ->
    (recInstance: RichRelationClass over recOb) ->
    RichRelationRecord over

mkRichRelation : (RichRelationClass over ob) => RichRelationRecord over
mkRichRelation {over} {ob} = MkRichRelation ob %instance

instance ObClass (RichRelationRecord over) where
  Ob = recOb

RichHom : (relation: RichRelationRecord over) -> RichRelation_Arrow over |relation|
RichHom relation = (:>) @{recInstance relation}

