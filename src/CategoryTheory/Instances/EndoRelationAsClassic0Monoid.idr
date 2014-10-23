module CategoryTheory.Instances.EndoRelationAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Classes.EndoRelation
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

data UnitMorphism : EndoRelation_Arrow unit 
  where
    MkUnitMorphism : UnitMorphism () ()

instance EndoRelationClass unit 
  where
    (|~>|) = UnitMorphism

UnitEndoRelation' : EndoRelationClass unit
UnitEndoRelation' = %instance

UnitEndoRelation : EndoRelationRecord
UnitEndoRelation = mkEndoRelation @{UnitEndoRelation'}

IsProductMorphism' :
  (EndoRelationClass left, EndoRelationClass right) =>
  EndoRelation_Arrow (left # right)
IsProductMorphism' (leftSource & rightSource) (leftTarget & rightTarget) =
  (leftSource |~>| leftTarget) # (rightSource |~>| rightTarget)

IsProductMorphism :
  (rLeft, rRight: EndoRelationRecord) -> 
  EndoRelation_Arrow ( |rLeft| # |rRight| )
IsProductMorphism rLeft rRight = 
  IsProductMorphism' @{recInstance rLeft} @{recInstance rRight}

data ProductMorphism : 
    (rLeft, rRight: EndoRelationRecord) -> 
    EndoRelation_Arrow ( |rLeft| # |rRight| )
  where
    MkProductMorphism : 
      {rLeft, rRight: EndoRelationRecord} -> 
      {source, target: |rLeft| # |rRight| } ->
      IsProductMorphism rLeft rRight source target ->
      ProductMorphism rLeft rRight source target                      

recMor : 
  {rLeft, rRight: EndoRelationRecord} -> 
  {source, target: |rLeft| # |rRight| } ->
  ProductMorphism rLeft rRight source target ->
  IsProductMorphism rLeft rRight source target
recMor (MkProductMorphism mor) = mor

instance (EndoRelationClass left, EndoRelationClass right) => 
    EndoRelationClass (left # right) 
  where
    (|~>|) = ProductMorphism (mkEndoRelation {ob = left}) (mkEndoRelation {ob = right})

ProductEndoRelation' : 
  (EndoRelationClass left, EndoRelationClass right) => EndoRelationClass (left # right)
ProductEndoRelation' {left} {right} = %instance

ProductEndoRelation : Classic0Monoid_Product EndoRelationRecord
ProductEndoRelation (rLeft, rRight) = 
  mkEndoRelation @{ProductEndoRelation' @{recInstance rLeft} @{recInstance rRight}}

instance Classic0MonoidClass EndoRelationRecord 
  where
    getUnit0 _ = UnitEndoRelation 
    getProduct0 = ProductEndoRelation

EndoRelationClassic0Monoid' : Classic0MonoidClass EndoRelationRecord
EndoRelationClassic0Monoid' = %instance

EndoRelationClassic0Monoid : Classic0MonoidRecord
EndoRelationClassic0Monoid = mkClassic0Monoid @{EndoRelationClassic0Monoid'}

