module CategoryTheory.Classes.EnrichedEndoRelation

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

EnrichedEndoRelation_Arrow : Type -> Type -> Type
EnrichedEndoRelation_Arrow over ob = ob ->> over

class EnrichedEndoRelationClass (over: Type) (ob: Type) 
  where
    (:>) : EnrichedEndoRelation_Arrow over ob

data EnrichedEndoRelationRecord : Type -> Type 
  where
    MkEnrichedEndoRelation : 
      {over: Type} ->
      (ob: Type) ->
      EnrichedEndoRelationClass over ob ->
      EnrichedEndoRelationRecord over

recOb : 
  {over: Type} -> 
  EnrichedEndoRelationRecord over -> 
  Type
recOb (MkEnrichedEndoRelation ob inst) = ob

recInstance : 
  {over: Type} -> 
  (rec: EnrichedEndoRelationRecord over) -> 
  EnrichedEndoRelationClass over (recOb rec)
recInstance (MkEnrichedEndoRelation ob inst) = inst

mkEnrichedEndoRelation : 
  (EnrichedEndoRelationClass over ob) => 
  EnrichedEndoRelationRecord over
mkEnrichedEndoRelation {over} {ob} = MkEnrichedEndoRelation ob %instance

instance ObClass (EnrichedEndoRelationRecord over) 
  where
    Ob = recOb

Hom : 
  (relation: EnrichedEndoRelationRecord over) -> 
  EnrichedEndoRelation_Arrow over |relation|
Hom relation = (:>) @{recInstance relation}

