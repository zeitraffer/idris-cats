module CategoryTheory.Instances.EnrichedEndoRelationAsClassic0Category

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Category
import CategoryTheory.Instances.EnrichedEndoRelationAsEndoRelation

%access public
%default total

------------------------------------------------------------

instance 
    (EndoRelationClass over, Classic0CategoryFullClass over (~>)) =>
    Classic0CategoryFullClass (EnrichedEndoRelationRecord over) (~>) 
  where

    getIdentity0 {over} rel ()
      = MkEnrichedEndoRelationMorphism 
        id 
        (\x,y => getIdentity0 
                 {ob = over} {to = (~>)} -- FIXME this should be inferred
                 (Hom rel x y) 
                 ())

    getMultiply0 {over} rel1 rel2 rel3 
        ((MkEnrichedEndoRelationMorphism map12 functor12) & 
         (MkEnrichedEndoRelationMorphism map23 functor23)) 
      = MkEnrichedEndoRelationMorphism 
        (map23 . map12)
        (\x,y => getMultiply0 
                 {ob = over} {to = (~>)} -- FIXME this should be inferred
                 (Hom rel1 x y) 
                 (Hom rel2 (map12 x) (map12 y)) 
                 (Hom rel3 (map23 (map12 x)) (map23 (map12 y)))
                 ((functor12 x y) & (functor23 (map12 x) (map12 y)))) 

EnrichedEndoRelationClassic0CategoryFull' : 
  (EndoRelationClass over, Classic0CategoryFullClass over (~>)) => 
  Classic0CategoryFullClass (EnrichedEndoRelationRecord over) (~>)
EnrichedEndoRelationClassic0CategoryFull' = %instance

EnrichedEndoRelationClassic0CategoryFull : Classic0CategoryShortRecord -> Classic0CategoryFullRecord
EnrichedEndoRelationClassic0CategoryFull rOver = 
  mkClassic0Category @{EnrichedEndoRelationClassic0CategoryFull' 
    @{castClassic0CategoryEndoRelation' @{recInstance rOver}} 
    @{castClassic0CategoryShortFull' @{recInstance rOver}}}

instance 
    (Classic0CategoryShortClass over) =>
    Classic0CategoryShortClass (EnrichedEndoRelationRecord over) 
  where {}

EnrichedEndoRelationClassic0CategoryShort' : 
  (Classic0CategoryShortClass over) => Classic0CategoryShortClass (EnrichedEndoRelationRecord over)
EnrichedEndoRelationClassic0CategoryShort' = %instance

EnrichedEndoRelationClassic0CategoryShort : Classic0CategoryShortRecord -> Classic0CategoryShortRecord
EnrichedEndoRelationClassic0CategoryShort rOver = 
  mkClassic0Category @{EnrichedEndoRelationClassic0CategoryShort' @{recInstance rOver}}

