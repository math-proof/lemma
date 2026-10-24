import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[threeGateCounter_boundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma threeGateCounter_boundaries_eq :
-- imply
  sources threeGateCounterEnds threeGateCounterSupport = {0, 2} /\ sources threeGateCounterEnds threeGateCounterK = {0, 1} /\ sources threeGateCounterEnds threeGateCounterS = {0, 1} /\ sources threeGateCounterEnds threeGateCounterN = {0, 2} /\ sources threeGateCounterEnds threeGateCounterA = {0, 2} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.threeGateCounter_boundaries

/--
[threeGateCounter_threefold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma threeGateCounter_threefold_eq :
-- imply
  threeGateCounterK ∆ threeGateCounterS ∆ threeGateCounterN = threeGateCounterA := by
-- proof
  apply StatMech.GrahamGHS.FourColor.threeGateCounter_threefold

/--
[threeGateCounter_K_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma threeGateCounter_K_gated_eq :
-- imply
  ThreeGateCounterGated threeGateCounterK := by
-- proof
  apply StatMech.GrahamGHS.FourColor.threeGateCounter_K_gated

/--
[threeGateCounter_S_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma threeGateCounter_S_gated_eq :
-- imply
  ThreeGateCounterGated threeGateCounterS := by
-- proof
  apply StatMech.GrahamGHS.FourColor.threeGateCounter_S_gated

/--
[threeGateCounter_N_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma threeGateCounter_N_gated_eq :
-- imply
  ThreeGateCounterGated threeGateCounterN := by
-- proof
  apply StatMech.GrahamGHS.FourColor.threeGateCounter_N_gated

/--
[threeGate_boundaryOnly_closure_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma threeGate_boundaryOnly_closure_false_eq :
-- imply
  sources threeGateCounterEnds threeGateCounterSupport = {0, 2} ∧ sources threeGateCounterEnds threeGateCounterK = {0, 1} ∧ sources threeGateCounterEnds threeGateCounterS = {0, 1} ∧ sources threeGateCounterEnds threeGateCounterN = {0, 2} ∧ threeGateCounterK ∆ threeGateCounterS ∆ threeGateCounterN = threeGateCounterA ∧ ThreeGateCounterGated threeGateCounterK ∧ ThreeGateCounterGated threeGateCounterS ∧ ThreeGateCounterGated threeGateCounterN ∧ ¬ ThreeGateCounterGated threeGateCounterA := by
-- proof
  apply StatMech.GrahamGHS.FourColor.threeGate_boundaryOnly_closure_false

/--
[canonicalGateCounter_rows_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_rows_partition_eq :
-- imply
  canonicalGateCounterSupport \ canonicalGateCounterK = canonicalGateCounterL ∧ canonicalGateCounterSupport \ canonicalGateCounterA = canonicalGateCounterB ∧ canonicalGateCounterSupport \ canonicalGateCounterS = canonicalGateCounterR := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_rows_partition

/--
[canonicalGateCounter_cells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_cells_eq :
-- imply
  canonicalGateCounterK ∩ canonicalGateCounterA = canonicalGateCounterC0 ∧ canonicalGateCounterK ∩ canonicalGateCounterB = canonicalGateCounterC1 ∧ canonicalGateCounterL ∩ canonicalGateCounterA = canonicalGateCounterC2 ∧ canonicalGateCounterL ∩ canonicalGateCounterB = canonicalGateCounterC3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_cells

/--
[canonicalGateCounter_cell_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_cell_sources_eq :
-- imply
  sources canonicalGateCounterEnds canonicalGateCounterC0 = {0, 1} ∧ sources canonicalGateCounterEnds canonicalGateCounterC1 = ∅ ∧ sources canonicalGateCounterEnds canonicalGateCounterC2 = {1, 2} ∧ sources canonicalGateCounterEnds canonicalGateCounterC3 = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_cell_sources

/--
[canonicalGateCounter_K_zeroComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_K_zeroComponent_eq :
-- imply
  edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_K_zeroComponent

/--
[canonicalGateCounter_L_kComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_L_kComponent_eq :
-- imply
  edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 = {6} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_L_kComponent

/--
[canonicalGateCounter_transfer_is_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_transfer_is_canonical_eq :
-- imply
  edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 ∪ edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 = canonicalGateCounterTransfer := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_transfer_is_canonical

/--
[canonicalGateCounter_transfer_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_transfer_rows_eq :
-- imply
  canonicalGateCounterA ∆ canonicalGateCounterTransfer = canonicalGateCounterS ∧ canonicalGateCounterB ∆ canonicalGateCounterTransfer = canonicalGateCounterR := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_transfer_rows

/--
[canonicalGateCounter_KL_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_KL_gated_eq :
-- imply
  CanonicalGateCounterGated canonicalGateCounterK := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_KL_gated

/--
[canonicalGateCounter_SR_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounter_SR_gated_eq :
-- imply
  CanonicalGateCounterGated canonicalGateCounterS := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounter_SR_gated

/--
[canonicalGate_cellStrengthening_not_sufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean)
-/
@[path]
private lemma canonicalGate_cellStrengthening_not_sufficient_eq :
-- imply
  canonicalGateCounterK ∩ canonicalGateCounterA = canonicalGateCounterC0 ∧ canonicalGateCounterK ∩ canonicalGateCounterB = canonicalGateCounterC1 ∧ canonicalGateCounterL ∩ canonicalGateCounterA = canonicalGateCounterC2 ∧ canonicalGateCounterL ∩ canonicalGateCounterB = canonicalGateCounterC3 ∧ sources canonicalGateCounterEnds canonicalGateCounterC0 = {0, 1} ∧ sources canonicalGateCounterEnds canonicalGateCounterC1 = ∅ ∧ sources canonicalGateCounterEnds canonicalGateCounterC2 = {1, 2} ∧ sources canonicalGateCounterEnds canonicalGateCounterC3 = ∅ ∧ (edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 ∪ edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 = canonicalGateCounterTransfer) ∧ canonicalGateCounterA ∆ canonicalGateCounterTransfer = canonicalGateCounterS ∧ canonicalGateCounterB ∆ canonicalGateCounterTransfer = canonicalGateCounterR ∧ CanonicalGateCounterGated canonicalGateCounterK ∧ CanonicalGateCounterGated canonicalGateCounterS ∧ ¬ CanonicalGateCounterGated canonicalGateCounterA := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGate_cellStrengthening_not_sufficient


-- created on 2026-10-23
