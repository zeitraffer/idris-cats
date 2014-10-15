module CategoryTheory.Concrete.EnrichedRelation

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

EnrichedRelation_Arrow : Type -> Type -> Type
EnrichedRelation_Arrow over ob = ob ->> over

class EnrichedRelationClass (over: Type) (ob: Type) where
  (:>) : EnrichedRelation_Arrow over ob

data EnrichedRelationRecord : Type -> Type where
  MkEnrichedRelation : 
    {over: Type} ->
    (recOb: Type) ->
    (recInstance: EnrichedRelationClass over recOb) ->
    EnrichedRelationRecord over

recOb : {over: Type} -> EnrichedRelationRecord over -> Type
recOb (MkEnrichedRelation ob inst) = ob

recInstance : {over: Type} -> (rec: EnrichedRelationRecord over) -> EnrichedRelationClass over (recOb rec)
recInstance (MkEnrichedRelation ob inst) = inst

mkEnrichedRelation : (EnrichedRelationClass over ob) => EnrichedRelationRecord over
mkEnrichedRelation {over} {ob} = MkEnrichedRelation ob %instance

instance ObClass (EnrichedRelationRecord over) where
  Ob = recOb

Hom : (relation: EnrichedRelationRecord over) -> EnrichedRelation_Arrow over |relation|
Hom relation = (:>) @{recInstance relation}

