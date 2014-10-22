module CategoryTheory.Instances.Classic0MonoidAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

instance Classic0MonoidClass () 
  where
    getUnit0 _ = ()
    getProduct0 _ = ()

UnitClassic0Monoid : Classic0MonoidRecord
UnitClassic0Monoid = mkClassic0Monoid {carrier = ()}

instance 
    (Classic0MonoidClass left, Classic0MonoidClass right) => 
    Classic0MonoidClass (left # right) 
  where
    getUnit0 _ = (unit, unit)
    getProduct0 ((leftA & rightA), (leftB & rightB)) = (leftA # leftB) & (rightA # rightB)

ProductClassic0Monoid' : 
  (Classic0MonoidClass left, Classic0MonoidClass right) => 
  Classic0MonoidClass (left # right)
ProductClassic0Monoid' {left} {right} = %instance

ProductClassic0Monoid : Classic0Monoid_Product Classic0MonoidRecord
ProductClassic0Monoid (rLeft, rRight) = 
  mkClassic0Monoid @{ProductClassic0Monoid' @{recInstance rLeft} @{recInstance rRight}}

instance Classic0MonoidClass Classic0MonoidRecord 
  where
    getUnit0 _ = UnitClassic0Monoid
    getProduct0 = ProductClassic0Monoid

Classic0MonoidClassic0Monoid' : Classic0MonoidClass Classic0MonoidRecord
Classic0MonoidClassic0Monoid' = %instance

Classic0MonoidClassic0Monoid : Classic0MonoidRecord
Classic0MonoidClassic0Monoid = mkClassic0Monoid @{Classic0MonoidClassic0Monoid'}

