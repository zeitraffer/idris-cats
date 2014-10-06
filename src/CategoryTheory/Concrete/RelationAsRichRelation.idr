module CategoryTheory.Concrete.RelationAsRichRelation

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.RelationAsRelation
import CategoryTheory.Concrete.RelationMorphismAsRelation
import CategoryTheory.Concrete.RichRelation

instance RichRelationClass Relation Relation where
  (:>) = RelationMorphismRelation

RelationRichRelation : RichRelation Relation
RelationRichRelation = MkRichRelation Relation RelationMorphismRelation

