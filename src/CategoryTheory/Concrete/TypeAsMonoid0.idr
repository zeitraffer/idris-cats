module CategoryTheory.Concrete.TypeAsMonoid0

import CategoryTheory.Concrete.Monoid0

%access public
%default total

------------------------------------------------------------

instance Monoid0Class Type where
  getUnit0 none = ()
  getProduct0 pair = (fst pair, snd pair)

TypeMonoid0 : Monoid0Record
TypeMonoid0 = mkMonoid0 {carrier = Type}

(&) : left -> right -> left # right
l & r = (l, r)

