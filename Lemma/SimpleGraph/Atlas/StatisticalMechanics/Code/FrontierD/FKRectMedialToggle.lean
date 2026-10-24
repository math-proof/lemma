import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle
open Finset StatMech StatMech.FrontierD


/--
[fkMedialTogglePairingAt_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean)
-/
@[path]
private lemma fkMedialTogglePairingAt_self_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialTogglePairingAt pairing v v = !pairing v := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingAt_self pairing v

/--
[fkMedialTogglePairingAt_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean)
-/
@[path]
private lemma fkMedialTogglePairingAt_of_ne_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v w : T.Vertex}
-- given
  (h : w ≠ v) :
-- imply
  fkMedialTogglePairingAt pairing v w = pairing w := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingAt_of_ne pairing h

/--
[fkRectTorusMedialEdgeEquiv_vertexOfEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean)
-/
@[path]
private lemma fkRectTorusMedialEdgeEquiv_vertexOfEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectTorusMedialEdgeEquiv R (fkRectMedialVertexOfEdge R e) = e := by
-- proof
  apply StatMech.FrontierD.fkRectTorusMedialEdgeEquiv_vertexOfEdge R e

/--
[fkRectConfigurationToMedialPairing_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean)
-/
@[path]
private lemma fkRectConfigurationToMedialPairing_insert_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (he : e ∉ F) :
-- imply
  fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F)) = fkMedialTogglePairingAt (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkRectMedialVertexOfEdge R e) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationToMedialPairing_insert R F e he


-- created on 2026-10-23
