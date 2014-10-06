module CategoryTheory.Concrete.TypeAsRichRelation

import CategoryTheory.Concrete.RichRelation
import CategoryTheory.Concrete.TypeAsRelation

instance RichRelationClass Type Type where
  (:>) = TypeMorphism

TypeRichRelation : RichRelation Type
TypeRichRelation = MkRichRelation Type TypeMorphism

