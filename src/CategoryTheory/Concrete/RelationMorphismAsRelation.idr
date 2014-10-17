module CategoryTheory.Concrete.RelationMorphismAsRelation

------------------------------------------------------------

import CategoryTheory.Concrete.RelationAsRelation

%access public
%default total

------------------------------------------------------------

RelationMorphism2' : 
  (RelationClass source, RelationClass target) =>
  RelationMorphism (mkRelation {ob = source}) (mkRelation {ob = target}) ->> 
  Type
RelationMorphism2' {source} {target} m1 m2 = 
  (o: source) -> (m1 $ o)~>(m2 $ o)

RelationMorphism2 : 
  {rSource, rTarget: RelationRecord} ->
  RelationMorphism rSource rTarget ->> 
  Type
RelationMorphism2 {rSource = MkRelation source sourceInst} 
                  {rTarget = MkRelation target targetInst} 
  = RelationMorphism2' @{sourceInst} @{targetInst}

instance RelationClass (RelationMorphism rSource rTarget) where 
  (~>) = RelationMorphism2

RelationMorphismRelation : RelationRecord ->> RelationRecord
RelationMorphismRelation rSource rTarget = 
  mkRelation {ob = RelationMorphism rSource rTarget}

