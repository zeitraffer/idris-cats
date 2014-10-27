module CategoryTheory.Instances.EnrichedGraphAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Instances.EnrichedGraphAsGraph

%access public
%default total

------------------------------------------------------------

instance (GraphClass over, Classic0CategoryFullClass over (|~>|)) =>
    Classic0CategoryFullClass (EnrichedGraphRecord over) (|~>|) 
  where

    getIdentity0 rel ()
      = MkEnrichedGraphMorphism 
        id 
        (\x,y => getIdentity0 {to = (|~>|)} -- FIXME this should be inferred
                 (Hom rel x y) 
                 () )

    getMultiply0 rel1 rel2 rel3 
        ((MkEnrichedGraphMorphism map12 functor12) & 
         (MkEnrichedGraphMorphism map23 functor23)) 
      = MkEnrichedGraphMorphism 
        (map23 . map12)
        (\x,y => getMultiply0 {to = (|~>|)} -- FIXME this should be inferred
                 (Hom rel1 x y)
                 (Hom rel2 (map12 x) (map12 y))
                 (Hom rel3 (map23 (map12 x)) (map23 (map12 y)))
                 ( (functor12 x y) & (functor23 (map12 x) (map12 y)) )) 

EnrichedGraphClassic0CategoryFull' : 
  (GraphClass over, Classic0CategoryFullClass over (|~>|)) => 
  Classic0CategoryFullClass (EnrichedGraphRecord over) (|~>|)
EnrichedGraphClassic0CategoryFull' = %instance

EnrichedGraphClassic0CategoryFull : Classic0CategoryShortRecord -> Classic0CategoryFullRecord
EnrichedGraphClassic0CategoryFull rOver = 
  mkClassic0Category @{EnrichedGraphClassic0CategoryFull' 
    @{castClassic0CategoryGraph' @{recInstance rOver}} 
    @{castClassic0CategoryShortFull' @{recInstance rOver}}}

instance (Classic0CategoryShortClass over) =>
    Classic0CategoryShortClass (EnrichedGraphRecord over) 
  where {}

EnrichedGraphClassic0CategoryShort' : 
  (Classic0CategoryShortClass over) => Classic0CategoryShortClass (EnrichedGraphRecord over)
EnrichedGraphClassic0CategoryShort' = %instance

EnrichedGraphClassic0CategoryShort : Classic0CategoryShortRecord -> Classic0CategoryShortRecord
EnrichedGraphClassic0CategoryShort rOver = 
  mkClassic0Category @{EnrichedGraphClassic0CategoryShort' @{recInstance rOver}}

