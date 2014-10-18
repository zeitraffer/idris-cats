module CategoryTheory.Concrete.EnrichedRelationAsCategory0

------------------------------------------------------------

import CategoryTheory.Concrete.Category0
import CategoryTheory.Concrete.EnrichedRelationAsRelation

%access public
%default total

------------------------------------------------------------

instance 
    (Category0ShortClass over) =>
    Category0FullClass (EnrichedRelationRecord over) (~>) 
  where

    getIdentity0 {over} rel ()
      = MkEnrichedRelationMorphism 
        id 
        (\x,y => getIdentity0 
                 {ob = over} {to = (~>)} -- FIXME this should be inferred
                 (Hom rel x y) 
                 ())

    getMultiply0 {over} rel1 rel2 rel3 
        ((MkEnrichedRelationMorphism map12 functor12) & 
         (MkEnrichedRelationMorphism map23 functor23)) 
      = MkEnrichedRelationMorphism 
        (map23 . map12)
        (\x,y => getMultiply0 
                 {ob = over} {to = (~>)} -- FIXME this should be inferred
                 (Hom rel1 x y) 
                 (Hom rel2 (map12 x) (map12 y)) 
                 (Hom rel3 (map23 (map12 x)) (map23 (map12 y)))
                 ((functor12 x y) & (functor23 (map12 x) (map12 y)))) 

EnrichedRelationCategory0' : 
  (Category0ShortClass over) => Category0FullClass (EnrichedRelationRecord over) (~>)
EnrichedRelationCategory0' = %instance

EnrichedRelationCategory0 : 
  Category0ShortRecord -> Category0FullRecord
EnrichedRelationCategory0 rOver = mkCategory0 @{EnrichedRelationCategory0' @{recInstance rOver}}

