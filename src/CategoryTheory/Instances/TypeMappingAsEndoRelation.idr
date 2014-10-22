module CategoryTheory.Instances.TypeMappingAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation

%access public
%default total

------------------------------------------------------------

data TypeMapping : EndoRelation_Arrow Type where
  MkTypeMapping : 
    {source, target: Type} ->
    (source -> target) ->
    TypeMapping source target

recMor : {source, target: Type} -> TypeMapping source target -> source -> target
recMor (MkTypeMapping mor) = mor

instance 
    Apply0Class 
      (TypeMapping source target) 
      source 
      target 
  where
    ($) = recMor

instance 
    EndoRelationClass 
      Type 
  where
    (~>) = TypeMapping

TypeEndoRelation' : EndoRelationClass Type
TypeEndoRelation' = %instance

TypeEndoRelation : EndoRelationRecord
TypeEndoRelation = mkEndoRelation @{TypeEndoRelation'}

