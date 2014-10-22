module CategoryTheory.Instances.TypeRelationAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation

%access public
%default total

------------------------------------------------------------

{-

data TypeRelation : EndoRelation_Arrow Type 
  where
    MkTypeRelation : 
      {source, target: Type} ->
      (source -> target -> Type) ->
      TypeRelation source target

recMor : 
  {source, target: Type} -> 
  TypeRelation source target -> 
  (source -> target -> Type)
recMor (MkTypeRelation mor) = mor

instance EndoRelationClass Type 
  where
    (~>) = TypeRelation

MappingEndoRelation' : EndoRelationClass Type
MappingEndoRelation' = %instance

MappingEndoRelation : EndoRelationRecord
MappingEndoRelation = mkEndoRelation @{MappingEndoRelation'}

-}
