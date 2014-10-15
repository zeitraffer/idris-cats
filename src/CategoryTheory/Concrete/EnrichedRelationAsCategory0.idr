module CategoryTheory.Concrete.EnrichedRelationAsCategory0

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.EnrichedRelationAsRelation

%access public
%default total

------------------------------------------------------------

{-

instance 
    (RelationClass over, Category0Class over (~>)) => 
    Category0Class (EnrichedRelationRecord over) (~>) 
  where

    getIdentity0 {over} (MkEnrichedRelation oOb oInst) _ 
      = MkEnrichedRelationMorphism @{%instance} @{oInst} @{oInst} 
        id 
        (\_, _ => jd {to = (~>)} {o = (:>) @{oInst} _ _})

    getMultiply0 (MkEnrichedRelation o1Ob o1Inst) 
                 (MkEnrichedRelation o2Ob o2Inst) 
                 (MkEnrichedRelation o3Ob o3Inst) 
        ((MkEnrichedRelationMorphism map12 congr12) & 
         (MkEnrichedRelationMorphism map23 congr23)) 
      = MkEnrichedRelationMorphism @{%instance} @{o1Inst} @{o3Inst} 
        (map23 . map12)
        (\_,_ => (congr12 _ _) >>> (congr23 _ _)) 

EnrichedRelationCategory0' : 
  (RelationClass over, Category0Class over (~>)) => 
  Category0Record
EnrichedRelationCategory0' {over} = mkCategory0 {ob = EnrichedRelationRecord over}

-}
