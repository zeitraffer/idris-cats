module CategoryTheory.Concrete.RichRelationAsCategory0

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.RichRelationAsRelation

%access public
%default total

------------------------------------------------------------

{-

instance 
    (RelationClass over, Category0Class over (~>)) => 
    Category0Class (RichRelationRecord over) (~>) 
  where

    getIdentity0 {over} (MkRichRelation oOb oInst) _ 
      = MkRichRelationMorphism @{%instance} @{oInst} @{oInst} 
        id 
        (\_, _ => jd {to = (~>)} {o = (:>) @{oInst} _ _})

    getMultiply0 (MkRichRelation o1Ob o1Inst) 
                 (MkRichRelation o2Ob o2Inst) 
                 (MkRichRelation o3Ob o3Inst) 
        ((MkRichRelationMorphism map12 congr12) & 
         (MkRichRelationMorphism map23 congr23)) 
      = MkRichRelationMorphism @{%instance} @{o1Inst} @{o3Inst} 
        (map23 . map12)
        (\_,_ => (congr12 _ _) >>> (congr23 _ _)) 

RichRelationCategory0' : 
  (RelationClass over, Category0Class over (~>)) => 
  Category0Record
RichRelationCategory0' {over} = mkCategory0 {ob = RichRelationRecord over}

-}
