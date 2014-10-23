module CategoryTheory.Classes.Classic0Category

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation
import CategoryTheory.Classes.Classic0CategoryFull
import CategoryTheory.Classes.Classic0CategoryShort

%access public
%default total

------------------------------------------------------------

castClassic0CategoryShortFull' : (Classic0CategoryShortClass ob) => Classic0CategoryFullClass ob (|~>|)
castClassic0CategoryShortFull' = %instance

castClassic0CategoryShortFull : Classic0CategoryShortRecord -> Classic0CategoryFullRecord
castClassic0CategoryShortFull rec = mkClassic0Category @{castClassic0CategoryShortFull' @{recInstance rec}}

instance Cast Classic0CategoryShortRecord Classic0CategoryFullRecord 
  where
    cast = castClassic0CategoryShortFull

castClassic0CategoryEndoRelation' : (Classic0CategoryShortClass ob) => EndoRelationClass ob
castClassic0CategoryEndoRelation' = %instance

castClassic0CategoryEndoRelation : Classic0CategoryShortRecord -> EndoRelationRecord
castClassic0CategoryEndoRelation rec = mkEndoRelation @{castClassic0CategoryEndoRelation' @{recInstance rec}}

instance Cast Classic0CategoryShortRecord EndoRelationRecord 
  where
    cast = castClassic0CategoryEndoRelation

