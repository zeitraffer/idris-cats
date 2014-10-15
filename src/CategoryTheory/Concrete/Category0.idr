module CategoryTheory.Concrete.Category0

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsRelation
import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

Category0_Identity : (ob: Type) -> (to: ob ->> Type) -> Type
Category0_Identity ob to = (o: ob) -> 
    unit -> (o `to` o)

Category0_Multiply : (ob: Type) -> (to: ob ->> Type) -> Type
Category0_Multiply ob to = (o1, o2, o3 : ob) -> 
    (o1 `to` o2) # (o2 `to` o3) -> (o1 `to` o3)

class 
    Category0Class (ob: Type) (to: ob ->> Type) 
  where
    getIdentity0 : Category0_Identity ob to
    getMultiply0 : Category0_Multiply ob to

data Category0Record : Type where
  MkCategory0 : 
    (recOb: Type) -> 
    (recTo: recOb ->> Type) -> 
    (recInstance: Category0Class recOb recTo) -> 
    Category0Record

recOb : Category0Record -> Type
recOb (MkCategory0 ob to inst) = ob

recTo : (rec: Category0Record) -> recOb rec ->> Type
recTo (MkCategory0 ob to inst) = to

recInstance : (rec: Category0Record) -> Category0Class (recOb rec) (recTo rec)
recInstance (MkCategory0 ob to inst) = inst

instance ObClass Category0Record where
  Ob = recOb

mkCategory0 : (Category0Class ob to) => Category0Record
mkCategory0 {ob} {to} = MkCategory0 ob to %instance

-- identity with implicit index
jd : (Category0Class ob to) => {o: ob} -> 
    (o `to` o)
jd {ob} {to} {o} = 
    getIdentity0 {ob=ob} {to=to} o ()

-- multiply with implicit index
(>>>) : (Category0Class ob to) => {o1, o2, o3 : ob} -> 
    (o1 `to` o2) -> (o2 `to` o3) -> (o1 `to` o3)
(>>>) {ob} {to} {o1} {o2} {o3} m12 m23 =
    getMultiply0 {ob=ob} {to=to} o1 o2 o3 (m12 & m23)

