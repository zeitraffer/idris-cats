module CategoryTheory.Common

infixr 1 ->>, ~>, :>, +>
infixl 15 $ 
infixl 9 #                 

(->>) : Type -> Type -> Type
node ->> edge = (source, target: node) -> edge

class PointedClass (t: Type) where
  pointed : t

instance PointedClass () where
  pointed = ()

class ObClass (t : Type) where
  Ob : t -> Type

instance ObClass Type where
  Ob x = x

syntax "|" [t] "|" = Ob t

class ApplyClass (map : Type) (source: Type) (target: Type) where
  ($) : map -> source -> target


