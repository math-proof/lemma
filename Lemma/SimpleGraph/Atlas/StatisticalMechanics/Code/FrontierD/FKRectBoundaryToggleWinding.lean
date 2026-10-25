import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBoundaryCycleClassWinding_eq_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBoundaryCycleClassWinding_eq_black_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBoundaryCycleClassWinding R pairing d.1 = fkRectBlackBoundaryCycleClassWinding R pairing d := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryCycleClassWinding_eq_black R pairing d

/--
[fkRectBlackBoundaryWeight_toggle_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_toggle_of_ne_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {v : R.medialTorus.Vertex}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hd0 : d ≠ fkMedialBlackDart0 v)
  (hd1 : d ≠ fkMedialBlackDart1 v) :
-- imply
  fkRectBlackBoundaryWeight R pairing d = fkRectBlackBoundaryWeight R (fkMedialTogglePairingAt pairing v) d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_toggle_of_ne R pairing v d hd0 hd1

/--
[fkRectBlackBoundaryWeight_closed_dart0_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_closed_dart0_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF

/--
[fkRectBlackBoundaryWeight_closed_dart1_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_closed_dart1_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF

/--
[fkRectBlackBoundaryWeight_toggle_pair_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_toggle_pair_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectBlackBoundaryWeight R (fkMedialTogglePairingAt (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkRectMedialVertexOfEdge R e)) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) + fkRectBlackBoundaryWeight R (fkMedialTogglePairingAt (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkRectMedialVertexOfEdge R e)) (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_toggle_pair_eq_zero R F e heF

/--
[fkRectBlackBoundaryCycleClassWinding_split_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleClassWinding_split_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hreach : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) = fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) + fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleClassWinding_split_of_reachable R F e heF hreach

/--
[fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_sameCycle_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hreach : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hd : ¬ (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).SameCycle (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) d) :
-- imply
  fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) d = fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_sameCycle R F e heF hreach d hd

/--
[fkRectInsertedWalk_oldBlackCycle_dependent_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectInsertedWalk_oldBlackCycle_dependent_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hreach : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  ¬ FKRectWindingIndependent (fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) d) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedWalk_oldBlackCycle_dependent_of_reachable R F e r heF hreach d

/--
[fkRectInsertedWalk_oldBlackBoundaryOrbit_dependent_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean)
-/
@[path]
private lemma fkRectInsertedWalk_oldBlackBoundaryOrbit_dependent_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hreach : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d.1)) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedWalk_oldBlackBoundaryOrbit_dependent_of_reachable R F e r heF hreach d


-- created on 2026-10-23
