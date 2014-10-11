module CategoryTheory.Concrete.Category0

import CategoryTheory.Concrete.TypeAsRelation
import CategoryTheory.Concrete.TypeAsMonoid0

Category0_Identity : (ob: Type) -> (to: ob ->> Type) -> Type
Category0_Identity ob to = (o: ob) -> 
    unit ~> (o `to` o)

Category0_Multiply : (ob: Type) -> (to: ob ->> Type) -> Type
Category0_Multiply ob to = (o1, o2, o3 : ob) -> 
    (o1 `to` o2) # (o2 `to` o3) ~> (o1 `to` o3)

IsCategory0 : (ob: Type) -> (to: ob ->> Type) -> Type
IsCategory0 ob to = 
  ( Category0_Identity ob to,
    Category0_Multiply ob to )

recIdentity : IsCategory0 ob to -> Category0_Identity ob to
recIdentity (i, m) = i

recMultiply : IsCategory0 ob to -> Category0_Multiply ob to
recMultiply (i, m) = m

record Category0Record : Type where
  MkCategory0 : 
    (recOb: Type) -> 
    (recTo: recOb ->> Type) -> 
    (recIsCategory: IsCategory0 recOb recTo) -> 
    Category0Record

instance ObClass Category0Record where
  Ob = recOb

class Category0Class (ob: Type) (to: ob ->> Type) where
  getCategory0 : IsCategory0 ob to

getIdentity0 : (Category0Class ob to) => Category0_Identity ob to
getIdentity0 = recIdentity getCategory0

getMultiply0 : (Category0Class ob to) => Category0_Multiply ob to
getMultiply0 = recMultiply getCategory0

id : (Category0Class ob to) => {o: ob} -> 
    (o `to` o)
id {ob} {to} {o} = 
    getIdentity0 {ob=ob} {to=to} o $ ()

(>>>) : (Category0Class ob to) => {o1, o2, o3 : ob} -> 
    (o1 `to` o2) -> (o2 `to` o3) -> (o1 `to` o3)
(>>>) {ob} {to} {o1} {o2} {o3} m12 m23 =
    getMultiply0 {ob=ob} {to=to} o1 o2 o3 $ (m12 & m23)

