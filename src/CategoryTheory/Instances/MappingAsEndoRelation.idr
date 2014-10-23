module CategoryTheory.Instances.MappingAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation

%access public
%default total

------------------------------------------------------------

data MappingOb = MkMappingOb Type

instance ObClass MappingOb 
  where
    Ob (MkMappingOb type) = type

data MappingMorphism : EndoRelation_Arrow MappingOb 
  where
    MkMappingMorphism : 
      {source, target: MappingOb} ->
      ( |source| -> |target| ) ->
      MappingMorphism source target

recMor : 
  {source, target: MappingOb} -> 
  MappingMorphism source target -> 
  ( |source| -> |target| )
recMor (MkMappingMorphism mor) = mor

instance Apply0Class (MappingMorphism source target) 
                     ( |source| )
                     ( |target| )
  where
    ($) = recMor

instance EndoRelationClass MappingOb 
  where
    (|~>|) = MappingMorphism

MappingEndoRelation' : EndoRelationClass MappingOb
MappingEndoRelation' = %instance

MappingEndoRelation : EndoRelationRecord
MappingEndoRelation = mkEndoRelation @{MappingEndoRelation'}

