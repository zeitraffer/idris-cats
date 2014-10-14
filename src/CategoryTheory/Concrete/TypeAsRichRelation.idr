module CategoryTheory.Concrete.TypeAsRichRelation

import CategoryTheory.Concrete.RichRelation
import CategoryTheory.Concrete.TypeAsRelation

%access public
%default total

------------------------------------------------------------

instance RichRelationClass Type Type where
  (:>) = TypeMorphism

TypeRichRelation : RichRelationRecord Type
TypeRichRelation = mkRichRelation {ob = Type}

