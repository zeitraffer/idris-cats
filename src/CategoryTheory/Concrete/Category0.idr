module CategoryTheory.Concrete.Category0

------------------------------------------------------------

import CategoryTheory.Concrete.Category0Full
import CategoryTheory.Concrete.Category0Short

%access public
%default total

------------------------------------------------------------

castCategory0ShortFull' : (Category0ShortClass ob) => Category0FullRecord
castCategory0ShortFull' {ob} = mkCategory0 {ob = ob} 

castCategory0ShortFull : Category0ShortRecord -> Category0FullRecord
castCategory0ShortFull rec = castCategory0ShortFull' @{recInstance rec}

instance Cast Category0ShortRecord Category0FullRecord where
  cast = castCategory0ShortFull

{-
castCategory0FullShort' : 
  (RelationClass ob, Category0FullClass ob (~>)) => 
  Category0ShortRecord
castCategory0FullShort' {ob} = mkCategory0 {ob = ob} 
-}


