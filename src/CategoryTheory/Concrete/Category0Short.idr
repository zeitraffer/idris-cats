module CategoryTheory.Concrete.Category0Short

------------------------------------------------------------

import CategoryTheory.Concrete.Category0Full

%access public
%default total

------------------------------------------------------------

class 
    (RelationClass ob, Category0FullClass ob (~>)) =>
    Category0ShortClass (ob: Type)
  where {}

data Category0ShortRecord : Type where
  MkCategory0Short :
    (ob: Type) -> 
    Category0ShortClass ob -> 
    Category0ShortRecord

recOb : Category0ShortRecord -> Type
recOb (MkCategory0Short ob inst) = ob

recInstance : (rec: Category0ShortRecord) -> Category0ShortClass (recOb rec)
recInstance (MkCategory0Short ob inst) = inst

instance ObClass Category0ShortRecord where
  Ob = recOb

mkCategory0 : (Category0ShortClass ob) => Category0ShortRecord
mkCategory0 {ob} = MkCategory0Short ob %instance

