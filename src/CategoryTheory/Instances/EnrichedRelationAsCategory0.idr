module CategoryTheory.Instances.EnrichedRelationAsCategory0

------------------------------------------------------------

import CategoryTheory.Classes.Category0
import CategoryTheory.Instances.EnrichedRelationAsRelation

%access public
%default total

------------------------------------------------------------

instance 
    (RelationClass over, Category0FullClass over (~>)) =>
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

EnrichedRelationCategory0Full' : 
  (RelationClass over, Category0FullClass over (~>)) => 
  Category0FullClass (EnrichedRelationRecord over) (~>)
EnrichedRelationCategory0Full' = %instance

EnrichedRelationCategory0Full : Category0ShortRecord -> Category0FullRecord
EnrichedRelationCategory0Full rOver = 
  mkCategory0 @{EnrichedRelationCategory0Full' 
    @{castCategory0Relation' @{recInstance rOver}} 
    @{castCategory0ShortFull' @{recInstance rOver}}}

instance 
    (Category0ShortClass over) =>
    Category0ShortClass (EnrichedRelationRecord over) 
  where {}

EnrichedRelationCategory0Short' : 
  (Category0ShortClass over) => Category0ShortClass (EnrichedRelationRecord over)
EnrichedRelationCategory0Short' = %instance

EnrichedRelationCategory0Short : Category0ShortRecord -> Category0ShortRecord
EnrichedRelationCategory0Short rOver = 
  mkCategory0 @{EnrichedRelationCategory0Short' @{recInstance rOver}}

