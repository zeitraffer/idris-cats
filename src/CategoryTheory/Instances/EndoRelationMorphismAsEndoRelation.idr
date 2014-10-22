module CategoryTheory.Instances.EndoRelationMorphismAsEndoRelation

------------------------------------------------------------

import CategoryTheory.Instances.EndoRelationAsEndoRelation

%access public
%default total

------------------------------------------------------------

EndoRelationMorphism2' : 
  (EndoRelationClass source, EndoRelationClass target) =>
  EndoRelationMorphism (mkEndoRelation {ob = source}) (mkEndoRelation {ob = target}) ->> 
  Type
EndoRelationMorphism2' {source} {target} m1 m2 = 
  (o: source) -> (m1 $ o)~>(m2 $ o)

EndoRelationMorphism2 : 
  {rSource, rTarget: EndoRelationRecord} ->
  EndoRelationMorphism rSource rTarget ->> 
  Type
EndoRelationMorphism2 {rSource = MkEndoRelation source sourceInst} 
                  {rTarget = MkEndoRelation target targetInst} 
  = EndoRelationMorphism2' @{sourceInst} @{targetInst}

instance EndoRelationClass (EndoRelationMorphism rSource rTarget) where 
  (~>) = EndoRelationMorphism2

EndoRelationMorphismEndoRelation' : 
  (rSource, rTarget: EndoRelationRecord) -> EndoRelationClass (EndoRelationMorphism rSource rTarget)
EndoRelationMorphismEndoRelation' rSource rTarget = %instance

EndoRelationMorphismEndoRelation : EndoRelationRecord ->> EndoRelationRecord
EndoRelationMorphismEndoRelation rSource rTarget = 
  mkEndoRelation @{EndoRelationMorphismEndoRelation' rSource rTarget}

