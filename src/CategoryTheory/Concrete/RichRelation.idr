module CategoryTheory.Concrete.RichRelation

import CategoryTheory.Common

RichRelation_Arrow : Type -> Type -> Type
RichRelation_Arrow over obj = obj ->> over

class RichRelationClass (over: Type) (obj: Type) where
  (:>) : RichRelation_Arrow over obj

record RichRelationRecord : Type -> Type where
  MkRichRelation : 
    {over: Type} ->
    (recObj: Type) ->
    (recInstance: RichRelationClass over recObj) ->
    RichRelationRecord over

instance ObClass (RichRelationRecord over) where
  Ob = recObj

