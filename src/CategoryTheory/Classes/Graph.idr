module CategoryTheory.Classes.Graph

------------------------------------------------------------

import CategoryTheory.Common

%access public
%default total

------------------------------------------------------------

Graph_Arrow : Type -> Type
Graph_Arrow ob = ob ->> Type

class GraphClass (ob: Type) 
  where
    (|~>|) : Graph_Arrow ob

data GraphRecord : Type 
  where
    MkGraph : 
      (ob: Type) ->
      GraphClass ob ->
      GraphRecord

recOb : GraphRecord -> Type
recOb (MkGraph ob inst) = ob

recInstance : 
  (rec: GraphRecord) -> 
  GraphClass (recOb rec)
recInstance (MkGraph ob inst) = inst

mkGraph : (GraphClass ob) => GraphRecord
mkGraph {ob} = MkGraph ob %instance

instance ObClass GraphRecord 
  where
    Ob = recOb

Hom : (relation: GraphRecord) -> Graph_Arrow |relation|
Hom relation = (|~>|) @{recInstance relation}

