import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PcUpperUncond.Part4
open MeasureTheory Filter Topology Finset Set SimpleGraph StatMech StatMech.FK


/--
[exists_far_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma exists_far_not_mem_eq
  {S : Set (Site 2)}
  {c a0 : ℤ}
-- given
  (hfin : S.Finite) :
-- imply
  ∃ N : ℤ, a0 ≤ N ∧ (![N, c] : Site 2) ∉ S := by
-- proof
  apply StatMech.FK.exists_far_not_mem S hfin c a0

/--
[exists_walk_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma exists_walk_exterior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ z : Site 2, (hypercubicLattice 2).Reachable o z ∧ z ∉ cluster 2 ω o := by
-- proof
  apply StatMech.FK.exists_walk_exterior o hfin

/--
[exists_closed_latticeCircuit_of_finite_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma exists_closed_latticeCircuit_of_finite_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧ ω ∈ closedCircuitEvent c := by
-- proof
  apply StatMech.FK.exists_closed_latticeCircuit_of_finite_cluster o hfin

/--
[exists_enclosing_closed_latticeCircuit_of_finite_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma exists_enclosing_closed_latticeCircuit_of_finite_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ z : Site 2, (∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧ ω ∈ closedCircuitEvent c) ∧ ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z ∧ ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
-- proof
  apply StatMech.FK.exists_enclosing_closed_latticeCircuit_of_finite_cluster o hfin

/--
[finiteCluster_subset_iUnion_closedCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma finiteCluster_subset_iUnion_closedCircuit_eq
  {o : Site 2} :
-- imply
  {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω o).Finite} ⊆ ⋃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u) (_ : c.IsCycle), closedCircuitEvent c := by
-- proof
  apply StatMech.FK.finiteCluster_subset_iUnion_closedCircuit o

/--
[compl_percolationEvent_eq_finiteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma compl_percolationEvent_eq_finiteCluster_eq :
-- imply
  (percolationEvent 2)ᶜ = {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω (origin 2)).Finite} := by
-- proof
  apply StatMech.FK.compl_percolationEvent_eq_finiteCluster

/--
[fkPcRatio_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcRatio_def_eq
  {d : ℕ}
  {p : ℝ} :
-- imply
  fkPcRatio d p = (2 * d : ℝ) * (1 - p) := by
-- proof
  apply StatMech.FK.fkPcRatio_def d p

/--
[fkPcSummand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcSummand_eq_eq
  {d : ℕ}
  {p : ℝ}
  {ℓ : ℕ} :
-- imply
  (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ := by
-- proof
  apply StatMech.FK.fkPcSummand_eq d p ℓ

/--
[fkPcUpperBound_eq_closedForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcUpperBound_eq_closedForm_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hx : ‖fkPcRatio d p‖ < 1) :
-- imply
  fkPcUpperBound d p = (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2 := by
-- proof
  apply StatMech.FK.fkPcUpperBound_eq_closedForm d p hx

/--
[fkPcRatio_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcRatio_tendsto_one_eq
  {d : ℕ} :
-- imply
  Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds 0) := by
-- proof
  apply StatMech.FK.fkPcRatio_tendsto_one d

/--
[fkPcClosedForm_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcClosedForm_tendsto_zero_eq :
-- imply
  Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
-- proof
  apply StatMech.FK.fkPcClosedForm_tendsto_zero

/--
[fkPcUpperBound_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcUpperBound_tendsto_one_eq
  {d : ℕ} :
-- imply
  Tendsto (fun p : ℝ => fkPcUpperBound d p) (nhds 1) (nhds 0) := by
-- proof
  apply StatMech.FK.fkPcUpperBound_tendsto_one d

/--
[exists_p_lt_one_fkPcUpperBound_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma exists_p_lt_one_fkPcUpperBound_lt_one_eq
  {d : ℕ} :
-- imply
  ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → fkPcUpperBound d p < 1 := by
-- proof
  apply StatMech.FK.exists_p_lt_one_fkPcUpperBound_lt_one d

/--
[fkPcUpperBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPcUpperBound_nonneg_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : p ≤ 1) :
-- imply
  0 ≤ fkPcUpperBound d p := by
-- proof
  apply StatMech.FK.fkPcUpperBound_nonneg d hp

/--
[fkTheta_pos_of_nonPercolationBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkTheta_pos_of_nonPercolationBound_eq
  {q : ℝ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hBound : FkNonPercolationBound q hp hp1 hq)
  (hsum : fkPcUpperBound 2 p < 1) :
-- imply
  0 < fkTheta 2 hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.fkTheta_pos_of_nonPercolationBound hp hp1 hq hBound hsum

/--
[fkSubcriticalSet_bddAbove'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkSubcriticalSet_bddAbove'_eq
  {d : ℕ}
  {q : ℝ} :
-- imply
  BddAbove (fkSubcriticalSet d q) := by
-- proof
  apply StatMech.FK.fkSubcriticalSet_bddAbove' d q

/--
[fkSubcriticalSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkSubcriticalSet_nonempty_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  (fkSubcriticalSet 2 q).Nonempty := by
-- proof
  apply StatMech.FK.fkSubcriticalSet_nonempty hq

/--
[not_mem_fkSubcriticalSet_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma not_mem_fkSubcriticalSet_of_fkTheta_pos_eq
  {q : ℝ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hθ : 0 < fkTheta 2 hp hp1 hq (q := q)) :
-- imply
  p ∉ fkSubcriticalSet 2 q := by
-- proof
  apply StatMech.FK.not_mem_fkSubcriticalSet_of_fkTheta_pos hp hp1 hq hθ

/--
[fkPc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPc_lt_one_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p → FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
-- imply
  fkPc 2 q < 1 := by
-- proof
  apply StatMech.FK.fkPc_lt_one hq hGeom

/--
[fkPc_pos_and_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean)
-/
@[path]
private lemma fkPc_pos_and_lt_one_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p → FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
-- imply
  0 < fkPc 2 q ∧ fkPc 2 q < 1 := by
-- proof
  apply StatMech.FK.fkPc_pos_and_lt_one hq hGeom


-- created on 2026-10-23
