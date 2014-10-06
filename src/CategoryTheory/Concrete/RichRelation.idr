module CategoryTheory.Concrete.RichRelation

import CategoryTheory.Common

IsRichRelation : Type -> Type -> Type
IsRichRelation over obj = obj ->> over

record RichRelation : Type -> Type where
  MkRichRelation : 
    {over: Type} ->
    (recObj: Type) ->
    (recIsRel: IsRichRelation over recObj) ->
    RichRelation over

instance ObClass (RichRelation over) where
  Ob = recObj

class RichRelationClass (over: Type) (obj: Type) where
  (:>) : IsRichRelation over obj

