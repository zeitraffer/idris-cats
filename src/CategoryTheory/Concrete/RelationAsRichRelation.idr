module CategoryTheory.Concrete.RelationAsRichRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.RelationAsRelation
import CategoryTheory.Concrete.RelationMorphismAsRelation
import CategoryTheory.Concrete.RichRelation

instance RichRelationClass RelationRecord RelationRecord where
  (:>) = RelationMorphismRelation

RelationRichRelation : RichRelationRecord RelationRecord
RelationRichRelation = mkRichRelation {ob = RelationRecord}

