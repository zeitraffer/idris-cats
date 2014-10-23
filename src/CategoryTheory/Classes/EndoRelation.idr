module CategoryTheory.Classes.EndoRelation

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

EndoRelation_Arrow : Type -> Type
EndoRelation_Arrow ob = ob ->> Type

class EndoRelationClass (ob: Type) 
  where
    (|~>|) : EndoRelation_Arrow ob

data EndoRelationRecord : Type 
  where
    MkEndoRelation : 
      (ob: Type) ->
      EndoRelationClass ob ->
      EndoRelationRecord

recOb : EndoRelationRecord -> Type
recOb (MkEndoRelation ob inst) = ob

recInstance : 
  (rec: EndoRelationRecord) -> 
  EndoRelationClass (recOb rec)
recInstance (MkEndoRelation ob inst) = inst

mkEndoRelation : (EndoRelationClass ob) => EndoRelationRecord
mkEndoRelation {ob} = MkEndoRelation ob %instance

instance ObClass EndoRelationRecord 
  where
    Ob = recOb

Hom : (relation: EndoRelationRecord) -> EndoRelation_Arrow |relation|
Hom relation = (|~>|) @{recInstance relation}

