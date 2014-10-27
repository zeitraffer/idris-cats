module CategoryTheory.Classes.Classic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Graph
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

castClassic0CategoryGraph' : (Classic0CategoryShortClass ob) => GraphClass ob
castClassic0CategoryGraph' = %instance

castClassic0CategoryGraph : Classic0CategoryShortRecord -> GraphRecord
castClassic0CategoryGraph rec = mkGraph @{castClassic0CategoryGraph' @{recInstance rec}}

instance Cast Classic0CategoryShortRecord GraphRecord 
  where
    cast = castClassic0CategoryGraph

