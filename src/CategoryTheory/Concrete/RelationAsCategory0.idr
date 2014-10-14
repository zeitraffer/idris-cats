module CategoryTheory.Concrete.RelationAsCategory0

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.RelationAsRelation

%access public
%default total

------------------------------------------------------------

instance Category0Class RelationRecord (~>) where

  getIdentity0 (MkRelation oOb oInst) _ 
    = MkRelationMorphism @{oInst} @{oInst} 
        id 
        (\x, y => id)

  getMultiply0 (MkRelation o1Ob o1Inst) 
               (MkRelation o2Ob o2Inst) 
               (MkRelation o3Ob o3Inst) 
      ((MkRelationMorphism map12 congr12) & 
       (MkRelationMorphism map23 congr23)) 
    = MkRelationMorphism @{o1Inst} @{o3Inst} 
        (map23 . map12)
        (\x, y => (congr23 _ _) . (congr12 _ _))

RelationCategory0 : Category0Record
RelationCategory0 = mkCategory0 {ob = RelationRecord}

