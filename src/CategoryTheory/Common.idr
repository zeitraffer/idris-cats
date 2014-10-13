module CategoryTheory.Common

infixr 1 ->>, ~>, :>, +>
infixl 15 $, $~
infixl 9 #, &, >>>              

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

class 
  Apply0Class (map : Type) 
              (obSource: Type) 
              (obTarget: Type) 
  where
    ($) : map -> obSource -> obTarget

class 
  (Apply0Class map obSource obTarget) =>
  Apply1Class (map : Type) 
              (obSource: Type) 
              (obTarget: Type) 
              (toSource: obSource ->> Type) 
              (toTarget: obTarget ->> Type)
  where
    ($~) : {xSource, xTarget: obSource} -> 
      (m: map) -> (xSource `toSource` xTarget) -> ((m $ xSource)`toTarget`(m $ xTarget))

liftUnit : {t: Type} -> t -> () -> t
liftUnit x = \ _ => x

