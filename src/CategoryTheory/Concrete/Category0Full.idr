module CategoryTheory.Concrete.Category0Full

------------------------------------------------------------

import CategoryTheory.Concrete.Relation
import CategoryTheory.Concrete.TypeAsRelation
import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.TypeAsMonoid0

%access public
%default total

------------------------------------------------------------

Category0_Identity : (ob: Type) -> (ob ->> Type) -> Type
Category0_Identity ob (~~>) = (o: ob) -> 
    unit -> (o ~~> o)

Category0_Multiply : (ob: Type) -> (ob ->> Type) -> Type
Category0_Multiply ob (~~>) = (o1, o2, o3 : ob) -> 
    (o1 ~~> o2) # (o2 ~~> o3) -> (o1 ~~> o3)

class 
    Category0FullClass (ob: Type) (to: ob ->> Type) 
  where
    getIdentity0 : Category0_Identity ob to
    getMultiply0 : Category0_Multiply ob to

data Category0FullRecord : Type where
  MkCategory0Full : 
    (ob: Type) -> 
    (to: ob ->> Type) -> 
    Category0FullClass ob to -> 
    Category0FullRecord

recOb : Category0FullRecord -> Type
recOb (MkCategory0Full ob to inst) = ob

recTo : (rec: Category0FullRecord) -> recOb rec ->> Type
recTo (MkCategory0Full ob to inst) = to

recInstance : (rec: Category0FullRecord) -> Category0FullClass (recOb rec) (recTo rec)
recInstance (MkCategory0Full ob to inst) = inst

instance ObClass Category0FullRecord where
  Ob = recOb

mkCategory0 : (Category0FullClass ob to) => Category0FullRecord
mkCategory0 {ob} {to} = MkCategory0Full ob to %instance

-- identity with implicit index
jd : (Category0FullClass ob to) => {o: ob} -> 
    (o `to` o)
jd {ob} {to} {o} = 
    getIdentity0 {ob=ob} {to=to} o ()

-- multiply with implicit index
(>>>) : (Category0FullClass ob to) => {o1, o2, o3 : ob} -> 
    (o1 `to` o2) -> (o2 `to` o3) -> (o1 `to` o3)
(>>>) {ob} {to} {o1} {o2} {o3} m12 m23 =
    getMultiply0 {ob=ob} {to=to} o1 o2 o3 (m12 & m23)

