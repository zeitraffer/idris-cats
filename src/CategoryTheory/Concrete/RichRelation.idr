module CategoryTheory.Concrete.RichRelation

import CategoryTheory.Common

IsRichRelation : Type -> Type -> Type
IsRichRelation over obj = obj ->> over

record RichRelationRecord : Type -> Type where
  MkRichRelation : 
    {over: Type} ->
    (recObj: Type) ->
    (recIsRel: IsRichRelation over recObj) ->
    RichRelationRecord over

instance ObClass (RichRelationRecord over) where
  Ob = recObj

class RichRelationClass (over: Type) (obj: Type) where
  (:>) : IsRichRelation over obj

