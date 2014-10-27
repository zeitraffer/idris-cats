module CategoryTheory.Instances.GraphAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Instances.GraphAsGraph

%access public
%default total

------------------------------------------------------------

instance Classic0CategoryFullClass GraphRecord (|~>|) 
  where

    getIdentity0 rec
      () 
      = MkGraphMorphism 
        id 
        (\x,y => id)

    getMultiply0 rec1 rec2 rec3 
      ( (MkGraphMorphism map12 functor12) & 
        (MkGraphMorphism map23 functor23) ) 
      = MkGraphMorphism
        ( map23 . map12 )
        ( \x,y => (functor23 (map12 x) (map12 y)) . (functor12 x y) )

GraphClassic0CategoryFull' : Classic0CategoryFullClass GraphRecord (|~>|)
GraphClassic0CategoryFull' = %instance

GraphClassic0CategoryFull : Classic0CategoryFullRecord
GraphClassic0CategoryFull = mkClassic0Category @{GraphClassic0CategoryFull'}

instance Classic0CategoryShortClass GraphRecord 
  where {}

GraphClassic0CategoryShort' : Classic0CategoryShortClass GraphRecord
GraphClassic0CategoryShort' = %instance

GraphClassic0CategoryShort : Classic0CategoryShortRecord
GraphClassic0CategoryShort = mkClassic0Category @{GraphClassic0CategoryShort'}

