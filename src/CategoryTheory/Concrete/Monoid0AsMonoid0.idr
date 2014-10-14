module CategoryTheory.Concrete.Monoid0AsMonoid0

import CategoryTheory.Concrete.Monoid0
import CategoryTheory.Concrete.TypeAsMonoid0

instance Monoid0Class () where
  getUnit0 _ = ()
  getProduct0 _ = ()

UnitMonoid0 : Monoid0_Unit Monoid0Record
UnitMonoid0 _ = mkMonoid0 {carrier = ()}

instance 
    (Monoid0Class left, Monoid0Class right) => 
    Monoid0Class (left # right) 
  where
    getUnit0 _ = (unit, unit)
    getProduct0 ((leftA & rightA), (leftB & rightB)) = (leftA # leftB) & (rightA # rightB)

ProductMonoid0' : (Monoid0Class left, Monoid0Class right) => Monoid0Record
ProductMonoid0' {left} {right} = mkMonoid0 {carrier = left # right}

ProductMonoid0 : Monoid0_Product Monoid0Record
ProductMonoid0 (rLeft, rRight) = ProductMonoid0' @{recInstance rLeft} @{recInstance rRight}

instance Monoid0Class Monoid0Record where
  getUnit0 = UnitMonoid0
  getProduct0 = ProductMonoid0

Monoid0Monoid0 : Monoid0Record
Monoid0Monoid0 = mkMonoid0 {carrier = Monoid0Record}

