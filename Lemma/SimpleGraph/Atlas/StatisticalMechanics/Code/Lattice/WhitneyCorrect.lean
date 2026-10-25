import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
open SimpleGraph Set StatMech StatMech.Lattice


/--
[whc_deleted_le_latticeMinusBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_deleted_le_latticeMinusBarrier_eq
  {H : SimpleGraph (Site 2)}
  {f g : Site 2} :
-- imply
  ((whb_faceRegion H).deleteEdges {s(f, g)}) ≤ latticeMinusBarrier {v | ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f v} := by
-- proof
  apply StatMech.Lattice.whc_deleted_le_latticeMinusBarrier H f g

/--
[whc_dualCross_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_dualCross_nil_eq
  {H : SimpleGraph (Site 2)}
  {x : Site 2} :
-- imply
  whc_dualCross H (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
-- proof
  apply StatMech.Lattice.whc_dualCross_nil H x

/--
[whc_dualCross_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_dualCross_cons_eq
  {H : SimpleGraph (Site 2)}
  {a b c : Site 2}
  {p : (hypercubicLattice 2).Walk b c}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  whc_dualCross H (Walk.cons hab p) = (if whc_isCross H a b then 1 else 0) + whc_dualCross H p := by
-- proof
  apply StatMech.Lattice.whc_dualCross_cons H hab p

/--
[whc_dualCross_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_dualCross_parity_eq
  {H : SimpleGraph (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (φ : Site 2 → Prop)
  (hcompat : whc_CompatColoring H φ) :
-- imply
  Even (whc_dualCross H w) ↔ (φ x ↔ φ y) := by
-- proof
  apply StatMech.Lattice.whc_dualCross_parity H φ hcompat w

/--
[whc_deleted_step_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_deleted_step_preserves_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
  {a b : Site 2}
-- given
  (φ : Site 2 → Prop)
  (hcut : whc_CutColoring H f0 g0 φ)
  (hab : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b) :
-- imply
  (φ a ↔ φ b) := by
-- proof
  apply StatMech.Lattice.whc_deleted_step_preserves H f0 g0 φ hcut hab

/--
[whc_deleted_walk_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_deleted_walk_preserves_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
  {x y : Site 2}
  {w : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Walk x y}
-- given
  (φ : Site 2 → Prop)
  (hcut : whc_CutColoring H f0 g0 φ) :
-- imply
  (φ x ↔ φ y) := by
-- proof
  apply StatMech.Lattice.whc_deleted_walk_preserves H f0 g0 φ hcut w

/--
[whc_deleted_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_deleted_separated_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (φ : Site 2 → Prop)
  (hcut : whc_CutColoring H f0 g0 φ)
  (hne : ¬ (φ f0 ↔ φ g0)) :
-- imply
  ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.whc_deleted_separated H f0 g0 φ hcut hne

/--
[whc_correctWhitney_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_correctWhitney_of_residue_eq
-- given
  (hres : whc_WhitneyColoringResidue) :
-- imply
  whb_CorrectWhitney := by
-- proof
  apply StatMech.Lattice.whc_correctWhitney_of_residue hres

/--
[whc_shared_hstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_shared_hstep_eq
  {a0 a1 b1 : ℤ} :
-- imply
  sharedPrimalEdge ![a0, a1] ![a0, b1] = s(![a0, max a1 b1], ![a0 + 1, max a1 b1]) := by
-- proof
  apply StatMech.Lattice.whc_shared_hstep a0 a1 b1

/--
[whc_shared_vstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_shared_vstep_eq
  {a0 b0 a1 : ℤ}
-- given
  (h : a0 ≠ b0) :
-- imply
  sharedPrimalEdge ![a0, a1] ![b0, a1] = s(![max a0 b0, a1], ![max a0 b0, a1 + 1]) := by
-- proof
  apply StatMech.Lattice.whc_shared_vstep a0 b0 a1 h

/--
[whc_site_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_site_eq_iff_eq
  {x : Site 2}
  {c d : ℤ} :
-- imply
  x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
-- proof
  apply StatMech.Lattice.whc_site_eq_iff x c d

/--
[whc_inv_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_inv_bottom_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  sharedPrimalEdge a b = s(![(0:ℤ), 0], ![1, 0]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
-- proof
  apply StatMech.Lattice.whc_inv_bottom a b hab

/--
[whc_inv_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_inv_right_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  sharedPrimalEdge a b = s(![(1:ℤ), 0], ![1, 1]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
-- proof
  apply StatMech.Lattice.whc_inv_right a b hab

/--
[whc_inv_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_inv_top_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  sharedPrimalEdge a b = s(![(1:ℤ), 1], ![0, 1]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), 1]) := by
-- proof
  apply StatMech.Lattice.whc_inv_top a b hab

/--
[whc_inv_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_inv_left_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  sharedPrimalEdge a b = s(![(0:ℤ), 1], ![0, 0]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(-1:ℤ), 0]) := by
-- proof
  apply StatMech.Lattice.whc_inv_left a b hab

/--
[whc_phiWitness_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_phiWitness_iff_eq
  {x : Site 2} :
-- imply
  whc_phiWitness x ↔ (x 0 = 0 ∧ x 1 = 0) := by
-- proof
  apply StatMech.Lattice.whc_phiWitness_iff x

/--
[whc_square_adj_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_square_adj_cases_eq
  {u v : Site 2}
-- given
  (h : (imageGraph jbc_Pce).Adj u v) :
-- imply
  (u = ![(0:ℤ), 0] ∧ v = ![1, 0]) ∨ (u = ![(1:ℤ), 0] ∧ v = ![0, 0]) ∨ (u = ![(1:ℤ), 0] ∧ v = ![1, 1]) ∨ (u = ![(1:ℤ), 1] ∧ v = ![1, 0]) ∨ (u = ![(1:ℤ), 1] ∧ v = ![0, 1]) ∨ (u = ![(0:ℤ), 1] ∧ v = ![1, 1]) ∨ (u = ![(0:ℤ), 1] ∧ v = ![0, 0]) ∨ (u = ![(0:ℤ), 0] ∧ v = ![0, 1]) := by
-- proof
  apply StatMech.Lattice.whc_square_adj_cases h

/--
[whc_square_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_square_mem_iff_eq
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ (imageGraph jbc_Pce).edgeSet ↔ e = s(![(0:ℤ), 0], ![1, 0]) ∨ e = s(![(1:ℤ), 0], ![1, 1]) ∨ e = s(![(1:ℤ), 1], ![0, 1]) ∨ e = s(![(0:ℤ), 1], ![0, 0]) := by
-- proof
  apply StatMech.Lattice.whc_square_mem_iff e

/--
[whc_shared_mem_square_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_shared_mem_square_iff_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  sharedPrimalEdge a b ∈ (imageGraph jbc_Pce).edgeSet ↔ (s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), 1]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(-1:ℤ), 0])) := by
-- proof
  apply StatMech.Lattice.whc_shared_mem_square_iff a b hab

/--
[whc_Htest_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_Htest_mem_eq
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ whc_Htest.edgeSet ↔ e ∈ (imageGraph jbc_Pce).edgeSet ∧ e ≠ s(![(0:ℤ), 0], ![1, 0]) := by
-- proof
  apply StatMech.Lattice.whc_Htest_mem e

/--
[whc_cross_or_bottom_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_cross_or_bottom_iff_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  (whc_isCross whc_Htest a b ∨ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1])) ↔ sharedPrimalEdge a b ∈ (imageGraph jbc_Pce).edgeSet := by
-- proof
  apply StatMech.Lattice.whc_cross_or_bottom_iff a b hab

/--
[whc_cutColoring_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_cutColoring_witness_eq :
-- imply
  whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] whc_phiWitness := by
-- proof
  apply StatMech.Lattice.whc_cutColoring_witness

/--
[whc_Htest_adj_of_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_Htest_adj_of_square_eq
  {u v : Site 2}
-- given
  (h : (imageGraph jbc_Pce).Adj u v)
  (hne : s(u, v) ≠ s(![(0:ℤ), 0], ![1, 0])) :
-- imply
  whc_Htest.Adj u v := by
-- proof
  apply StatMech.Lattice.whc_Htest_adj_of_square u v h hne

/--
[whc_Htest_reach_pq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_Htest_reach_pq_eq :
-- imply
  whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.whc_Htest_reach_pq

/--
[whc_phiWitness_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_phiWitness_diff_eq :
-- imply
  ¬ (whc_phiWitness ![(0:ℤ), 0] ↔ whc_phiWitness ![(0:ℤ), -1]) := by
-- proof
  apply StatMech.Lattice.whc_phiWitness_diff

/--
[whc_residue_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_residue_witness_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ whc_Htest.edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧ (∃ φ : Site 2 → Prop, whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] φ ∧ (whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ↔ ¬ (φ ![(0:ℤ), 0] ↔ φ ![(0:ℤ), -1]))) := by
-- proof
  apply StatMech.Lattice.whc_residue_witness

/--
[whc_faithful_square_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean)
-/
@[path]
private lemma whc_faithful_square_nonempty_eq :
-- imply
  Nonempty {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite} := by
-- proof
  apply StatMech.Lattice.whc_faithful_square_nonempty


-- created on 2026-10-23
