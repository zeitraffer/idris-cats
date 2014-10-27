module CategoryTheory.Instances.GraphAsClassic0Monoid

------------------------------------------------------------

import CategoryTheory.Classes.Classic0Monoid
import CategoryTheory.Classes.Graph
import CategoryTheory.Instances.TypeAsClassic0Monoid

%access public
%default total

------------------------------------------------------------

data UnitMorphism : Graph_Arrow unit 
  where
    MkUnitMorphism : UnitMorphism () ()

instance GraphClass unit 
  where
    (|~>|) = UnitMorphism

UnitGraph' : GraphClass unit
UnitGraph' = %instance

UnitGraph : GraphRecord
UnitGraph = mkGraph @{UnitGraph'}

IsProductMorphism' :
  (GraphClass left, GraphClass right) =>
  Graph_Arrow (left # right)
IsProductMorphism' (leftSource & rightSource) (leftTarget & rightTarget) =
  (leftSource |~>| leftTarget) # (rightSource |~>| rightTarget)

IsProductMorphism :
  (rLeft, rRight: GraphRecord) -> 
  Graph_Arrow ( |rLeft| # |rRight| )
IsProductMorphism rLeft rRight = 
  IsProductMorphism' @{recInstance rLeft} @{recInstance rRight}

data ProductMorphism : 
    (rLeft, rRight: GraphRecord) -> 
    Graph_Arrow ( |rLeft| # |rRight| )
  where
    MkProductMorphism : 
      {rLeft, rRight: GraphRecord} -> 
      {source, target: |rLeft| # |rRight| } ->
      IsProductMorphism rLeft rRight source target ->
      ProductMorphism rLeft rRight source target                      

recMor : 
  {rLeft, rRight: GraphRecord} -> 
  {source, target: |rLeft| # |rRight| } ->
  ProductMorphism rLeft rRight source target ->
  IsProductMorphism rLeft rRight source target
recMor (MkProductMorphism mor) = mor

instance (GraphClass left, GraphClass right) => 
    GraphClass (left # right) 
  where
    (|~>|) = ProductMorphism (mkGraph {ob = left}) (mkGraph {ob = right})

ProductGraph' : 
  (GraphClass left, GraphClass right) => GraphClass (left # right)
ProductGraph' {left} {right} = %instance

ProductGraph : Classic0Monoid_Product GraphRecord
ProductGraph (rLeft, rRight) = 
  mkGraph @{ProductGraph' @{recInstance rLeft} @{recInstance rRight}}

instance Classic0MonoidClass GraphRecord 
  where
    getUnit0 _ = UnitGraph 
    getProduct0 = ProductGraph

GraphClassic0Monoid' : Classic0MonoidClass GraphRecord
GraphClassic0Monoid' = %instance

GraphClassic0Monoid : Classic0MonoidRecord
GraphClassic0Monoid = mkClassic0Monoid @{GraphClassic0Monoid'}

