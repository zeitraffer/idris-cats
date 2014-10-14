module CategoryTheory.Concrete.Category0

import CategoryTheory.Concrete.TypeAsRelation
import CategoryTheory.Concrete.TypeAsMonoid0

Category0_Identity : (ob: Type) -> (to: ob ->> Type) -> Type
Category0_Identity ob to = (o: ob) -> 
    unit ~> (o `to` o)

Category0_Multiply : (ob: Type) -> (to: ob ->> Type) -> Type
Category0_Multiply ob to = (o1, o2, o3 : ob) -> 
    (o1 `to` o2) # (o2 `to` o3) ~> (o1 `to` o3)

class Category0Class (ob: Type) (to: ob ->> Type) where
  getIdentity0 : Category0_Identity ob to
  getMultiply0 : Category0_Multiply ob to

record Category0Record : Type where
  MkCategory0 : 
    (recOb: Type) -> 
    (recTo: recOb ->> Type) -> 
    (recInstance: Category0Class recOb recTo) -> 
    Category0Record

instance ObClass Category0Record where
  Ob = recOb

mkCategory0 : (Category0Class ob to) => Category0Record
mkCategory0 {ob} {to} = MkCategory0 ob to %instance

-- identity with implicit index
id : (Category0Class ob to) => {o: ob} -> 
    (o `to` o)
id {ob} {to} {o} = 
    getIdentity0 {ob=ob} {to=to} o $ ()

-- multiply with implicit index
(>>>) : (Category0Class ob to) => {o1, o2, o3 : ob} -> 
    (o1 `to` o2) -> (o2 `to` o3) -> (o1 `to` o3)
(>>>) {ob} {to} {o1} {o2} {o3} m12 m23 =
    getMultiply0 {ob=ob} {to=to} o1 o2 o3 $ (m12 & m23)

