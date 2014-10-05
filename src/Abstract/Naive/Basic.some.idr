-- 
-- defines a basic category structure 
--

module Abstract.Naive.Basic

infix class => ~>
class Ob Carrier

-- instance Type (One, #, ~>)

signature Monoid0
    (class carrier : Type)
  where
    One : carrier
    (#) : carrier -> carrier -> carrier

signature
  (Graph Type, Monoid0 Type) 
  Category0
    (class ob : Type) 
    (implicit class (~>) : ob ->> Type) 
  where
    IdEqu : {o : ob} -> one ~> (o~>o)      
    MulEqu : {o1, o2, o3 : ob} -> (o1~>o2) # (o2~>o3) ~> (o1~>o3)
  
signature 
  (Graph over, Monoid0 over) =>
  RichCategory0
    {over : Type}
    (class ob : Type) 
    (implicit class (~>) : ob ->> over) 
  where
    IdEqu : {o : ob} -> one ~> (o~>o)      
    MulEqu : {o1, o2, o3 : ob} -> (o1~>o2) # (o2~>o3) ~> (o1~>o3)
  
signature 
  (Category0 (...)) => 
  Groupoid0
    (class ob : Type) 
    (implicit class (~>) : ob ->> Type) 
  where
    InvEqu : {o1, o2 : ob} -> (o1~>o2) ~> (o2~>o1)
  
signature 
  (Graph Type) =>
  CatMap0
    {c1, c2 : Category0} 
    (class obMap : ob c1 -> ob c2)
  where
    ApplyEqu : {o1, o2 : ob c1} -> (o1 ~> o2) ~> (obMap o1 ~> obMap o2)

-- instance Setoid (1, #, ~>)

signature 
  (RichCategory0 ob (~>)) =>
  Category1
    (class ob : Type) 
    (implicit class (~>) : ob ->> Setoid)
  where
    IdNeutralLeft : 
      {o1, o2 : ob} ->
      (m : o1 ~> o2) :~> (1 >>> m ~> m)
