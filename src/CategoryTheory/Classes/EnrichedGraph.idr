module CategoryTheory.Classes.EnrichedGraph

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

EnrichedGraph_Arrow : Type -> Type -> Type
EnrichedGraph_Arrow over ob = ob ->> over

class EnrichedGraphClass (over: Type) (ob: Type) 
  where
    (~>) : EnrichedGraph_Arrow over ob

data EnrichedGraphRecord : Type -> Type 
  where
    MkEnrichedGraph : 
      {over: Type} ->
      (ob: Type) ->
      EnrichedGraphClass over ob ->
      EnrichedGraphRecord over

recOb : 
  {over: Type} -> 
  EnrichedGraphRecord over -> 
  Type
recOb (MkEnrichedGraph ob inst) = ob

recInstance : 
  {over: Type} -> 
  (rec: EnrichedGraphRecord over) -> 
  EnrichedGraphClass over (recOb rec)
recInstance (MkEnrichedGraph ob inst) = inst

mkEnrichedGraph : 
  (EnrichedGraphClass over ob) => 
  EnrichedGraphRecord over
mkEnrichedGraph {over} {ob} = MkEnrichedGraph ob %instance

instance ObClass (EnrichedGraphRecord over) 
  where
    Ob = recOb

Hom : 
  (relation: EnrichedGraphRecord over) -> 
  EnrichedGraph_Arrow over |relation|
Hom relation = (~>) @{recInstance relation}

