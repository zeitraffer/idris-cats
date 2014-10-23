module CategoryTheory.Classes.Classic0CategoryFull

------------------------------------------------------------

import CategoryTheory.Classes.EndoRelation
import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Instances.MappingAsEndoRelation
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

Classic0Category_Identity : (ob: Type) -> (ob ->> Type) -> Type
Classic0Category_Identity ob (>-) = (o: ob) -> 
    unit -> (o >- o)

Classic0Category_Multiply : (ob: Type) -> (ob ->> Type) -> Type
Classic0Category_Multiply ob (>-) = (o1, o2, o3 : ob) -> 
    (o1 >- o2) # (o2 >- o3) -> (o1 >- o3)

class Classic0CategoryFullClass (ob: Type) (to: ob ->> Type) 
  where
    getIdentity0 : Classic0Category_Identity ob to
    getMultiply0 : Classic0Category_Multiply ob to

data Classic0CategoryFullRecord : Type 
  where
    MkClassic0CategoryFull : 
      (ob: Type) -> 
      (to: ob ->> Type) -> 
      Classic0CategoryFullClass ob to -> 
      Classic0CategoryFullRecord

recOb : Classic0CategoryFullRecord -> Type
recOb (MkClassic0CategoryFull ob to inst) = ob

recTo : 
  (rec: Classic0CategoryFullRecord) -> 
  recOb rec ->> Type
recTo (MkClassic0CategoryFull ob to inst) = to

recInstance : 
  (rec: Classic0CategoryFullRecord) -> 
  Classic0CategoryFullClass (recOb rec) (recTo rec)
recInstance (MkClassic0CategoryFull ob to inst) = inst

instance ObClass Classic0CategoryFullRecord 
  where
    Ob = recOb

mkClassic0Category : (Classic0CategoryFullClass ob to) => Classic0CategoryFullRecord
mkClassic0Category {ob} {to} = MkClassic0CategoryFull ob to %instance

-- identity with implicit index
id' : (Classic0CategoryFullClass ob to) => {o: ob} -> 
    (o `to` o)
id' {ob} {to} {o} = 
    getIdentity0 {ob=ob} {to=to} o ()

-- multiplication with implicit index
(>>>) : (Classic0CategoryFullClass ob to) => {o1, o2, o3 : ob} -> 
    (o1 `to` o2) -> (o2 `to` o3) -> (o1 `to` o3)
(>>>) {ob} {to} {o1} {o2} {o3} m12 m23 =
    getMultiply0 {ob=ob} {to=to} o1 o2 o3 (m12 & m23)

