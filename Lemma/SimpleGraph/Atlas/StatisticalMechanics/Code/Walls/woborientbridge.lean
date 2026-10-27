import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.woborientbridge.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wob_rayEdge_eq_hCrossEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_rayEdge_eq_hCrossEdge_eq
  {z : Site 2}
  {c : ℤ} :
-- imply
  wcb_canonRayEdge z c = rpc_hCrossEdge (![c, z 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wob_rayEdge_eq_hCrossEdge z c

/--
[wob_signStep_ne_zero_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_signStep_ne_zero_col_eq
  {z u v : Site 2}
-- given
  (h : wnd_signStep z u v ≠ 0) :
-- imply
  jec_rayEdge z s(u, v) := by
-- proof
  apply StatMech.Lattice.wob_signStep_ne_zero_col z u v h

/--
[wob_indJump_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_indJump_mem_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c : ℤ} :
-- imply
  wob_indJump z Vc c = 1 ∨ wob_indJump z Vc c = 0 ∨ wob_indJump z Vc c = -1 := by
-- proof
  apply StatMech.Lattice.wob_indJump_mem z Vc c

/--
[wob_indJump_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_indJump_ne_zero_iff_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c : ℤ} :
-- imply
  wob_indJump z Vc c ≠ 0 ↔ Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) := by
-- proof
  apply StatMech.Lattice.wob_indJump_ne_zero_iff z Vc c

/--
[wob_indJump_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_indJump_parity_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c : ℤ} :
-- imply
  wob_indJump z Vc c % 2 = (if Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) then (1 : ℤ) else 0) % 2 := by
-- proof
  apply StatMech.Lattice.wob_indJump_parity z Vc c

/--
[wob_columnSortedEqJumps_iff_orientationConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_columnSortedEqJumps_iff_orientationConsistent_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  wob_ColumnSortedEqJumps z Vc ↔ wel_OrientationConsistent z Vc := by
-- proof
  apply StatMech.Lattice.wob_columnSortedEqJumps_iff_orientationConsistent z Vc

/--
[wob_orientationConsistent_of_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_orientationConsistent_of_columnSortedEqJumps_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wob_ColumnSortedEqJumps z Vc) :
-- imply
  wel_OrientationConsistent z Vc := by
-- proof
  apply StatMech.Lattice.wob_orientationConsistent_of_columnSortedEqJumps z Vc h

/--
[wob_signsAlternate_of_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_signsAlternate_of_columnSortedEqJumps_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wob_ColumnSortedEqJumps z Vc) :
-- imply
  wos_SignsAlternateInColumnOrder z Vc := by
-- proof
  apply StatMech.Lattice.wob_signsAlternate_of_columnSortedEqJumps z Vc h

/--
[wob_columnAlternates_of_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_columnAlternates_of_columnSortedEqJumps_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wob_ColumnSortedEqJumps z Vc) :
-- imply
  wna_ColumnAlternates z Vc := by
-- proof
  apply StatMech.Lattice.wob_columnAlternates_of_columnSortedEqJumps z Vc h

/--
[wob_signedCross_pm_one_of_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_signedCross_pm_one_of_columnSortedEqJumps_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wob_ColumnSortedEqJumps z Vc)
  (hodd : ¬ Even (jec_rayCount z Vc)) :
-- imply
  wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 := by
-- proof
  apply StatMech.Lattice.wob_signedCross_pm_one_of_columnSortedEqJumps z Vc h hodd

/--
[wob_orientationConsistent_of_signStepMatchesJump](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_orientationConsistent_of_signStepMatchesJump_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wob_SignStepMatchesJump z Vc) :
-- imply
  wel_OrientationConsistent z Vc := by
-- proof
  apply StatMech.Lattice.wob_orientationConsistent_of_signStepMatchesJump z Vc h

/--
[wob_canonicalUpDart_signStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_canonicalUpDart_signStep_eq
  {z : Site 2}
  {c : ℤ}
-- given
  (hc : c ≤ z 0 - 1) :
-- imply
  wnd_signStep z (![c, z 1 - 1] : Site 2) (![c, z 1] : Site 2) = 1 := by
-- proof
  apply StatMech.Lattice.wob_canonicalUpDart_signStep z c hc

/--
[wob_canonicalUpDart_signStep_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_canonicalUpDart_signStep_zero_eq
  {z : Site 2}
  {c : ℤ}
-- given
  (hc : z 0 - 1 < c) :
-- imply
  wnd_signStep z (![c, z 1 - 1] : Site 2) (![c, z 1] : Site 2) = 0 := by
-- proof
  apply StatMech.Lattice.wob_canonicalUpDart_signStep_zero z c hc

/--
[wob_unitSquare_indSeq0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_unitSquare_indSeq0_eq :
-- imply
  wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 0 = 0 := by
-- proof
  apply StatMech.Lattice.wob_unitSquare_indSeq0

/--
[wob_unitSquare_indSeq1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_unitSquare_indSeq1_eq :
-- imply
  wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 1 = 1 := by
-- proof
  apply StatMech.Lattice.wob_unitSquare_indSeq1

/--
[wob_unitSquare_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_unitSquare_columnSortedEqJumps_eq :
-- imply
  wob_ColumnSortedEqJumps (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wob_unitSquare_columnSortedEqJumps

/--
[wob_Ltromino_indSeq0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_Ltromino_indSeq0_eq :
-- imply
  wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 0 = 0 := by
-- proof
  apply StatMech.Lattice.wob_Ltromino_indSeq0

/--
[wob_Ltromino_indSeq1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_Ltromino_indSeq1_eq :
-- imply
  wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 1 = 1 := by
-- proof
  apply StatMech.Lattice.wob_Ltromino_indSeq1

/--
[wob_Ltromino_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_Ltromino_columnSortedEqJumps_eq :
-- imply
  wob_ColumnSortedEqJumps (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wob_Ltromino_columnSortedEqJumps

/--
[wob_doubleSquare_not_columnSortedEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean)
-/
@[path]
private lemma wob_doubleSquare_not_columnSortedEqJumps_eq :
-- imply
  ¬ wob_ColumnSortedEqJumps (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wob_doubleSquare_not_columnSortedEqJumps


-- created on 2026-10-23
