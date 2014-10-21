module CategoryTheory.Instances.TypeAsMonoid0

------------------------------------------------------------

import CategoryTheory.Classes.Monoid0

%access public
%default total

------------------------------------------------------------

instance Monoid0Class Type where
  getUnit0 none = ()
  getProduct0 pair = (fst pair, snd pair)

TypeMonoid0' : Monoid0Class Type
TypeMonoid0' = %instance

TypeMonoid0 : Monoid0Record
TypeMonoid0 = mkMonoid0 @{TypeMonoid0'}

(&) : left -> right -> left # right
l & r = (l, r)

