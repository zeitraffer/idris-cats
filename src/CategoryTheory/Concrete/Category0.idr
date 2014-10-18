module CategoryTheory.Concrete.Category0

------------------------------------------------------------

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.Category0Full
import CategoryTheory.Concrete.Category0Short

%access public
%default total

------------------------------------------------------------

castCategory0ShortFull' : (Category0ShortClass ob) => Category0FullClass ob (~>)
castCategory0ShortFull' = %instance

castCategory0ShortFull : Category0ShortRecord -> Category0FullRecord
castCategory0ShortFull rec = mkCategory0 @{castCategory0ShortFull' @{recInstance rec}}

instance Cast Category0ShortRecord Category0FullRecord where
  cast = castCategory0ShortFull

castCategory0Relation' : (Category0ShortClass ob) => RelationClass ob
castCategory0Relation' = %instance

castCategory0Relation : Category0ShortRecord -> RelationRecord
castCategory0Relation rec = mkRelation @{castCategory0Relation' @{recInstance rec}}

instance Cast Category0ShortRecord RelationRecord where
  cast = castCategory0Relation

