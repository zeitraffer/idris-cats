module CategoryTheory.Instances.TypeAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Monoid

%access public
%default total

------------------------------------------------------------

instance Classic0MonoidClass Type where
  getUnit0 none = ()
  getProduct0 pair = (fst pair, snd pair)

TypeClassic0Monoid' : Classic0MonoidClass Type
TypeClassic0Monoid' = %instance

TypeClassic0Monoid : Classic0MonoidRecord
TypeClassic0Monoid = mkClassic0Monoid @{TypeClassic0Monoid'}

(&) : left -> right -> left # right
l & r = (l, r)

