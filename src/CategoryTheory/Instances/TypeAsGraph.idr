module CategoryTheory.Instances.TypeAsGraph

------------------------------------------------------------

import CategoryTheory.Common
import CategoryTheory.Classes.Graph

%access public
%default total

------------------------------------------------------------

data TypeMorphism : Graph_Arrow Type 
  where
    MkTypeMorphism : 
      {source, target: Type} ->
      ( |source| -> |target| ) ->
      TypeMorphism source target

recMor : 
  {source, target: Type} -> 
  TypeMorphism source target -> 
  ( |source| -> |target| )
recMor (MkTypeMorphism mor) = mor

instance Apply0Class (TypeMorphism source target) 
                     ( |source| )
                     ( |target| )
  where
    ($) = recMor

instance GraphClass Type 
  where
    (|~>|) = TypeMorphism

TypeGraph' : GraphClass Type
TypeGraph' = %instance

TypeGraph : GraphRecord
TypeGraph = mkGraph @{TypeGraph'}

