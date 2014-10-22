module CategoryTheory.Classes.Classic0CategoryShort

------------------------------------------------------------

import CategoryTheory.Classes.Classic0CategoryFull

%access public
%default total

------------------------------------------------------------

class 
    (EndoRelationClass ob, Classic0CategoryFullClass ob (~>)) =>
    Classic0CategoryShortClass (ob: Type)
  where {}

data Classic0CategoryShortRecord : Type where
  MkClassic0CategoryShort :
    (ob: Type) -> 
    Classic0CategoryShortClass ob -> 
    Classic0CategoryShortRecord

recOb : Classic0CategoryShortRecord -> Type
recOb (MkClassic0CategoryShort ob inst) = ob

recInstance : (rec: Classic0CategoryShortRecord) -> Classic0CategoryShortClass (recOb rec)
recInstance (MkClassic0CategoryShort ob inst) = inst

instance ObClass Classic0CategoryShortRecord where
  Ob = recOb

mkClassic0Category : (Classic0CategoryShortClass ob) => Classic0CategoryShortRecord
mkClassic0Category {ob} = MkClassic0CategoryShort ob %instance

