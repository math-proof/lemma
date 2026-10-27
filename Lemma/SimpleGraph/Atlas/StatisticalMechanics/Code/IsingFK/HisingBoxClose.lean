import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
open StatMech StatMech.IsingFK


/--
[hbx_mem_bondFinsetTouch_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_mem_bondFinsetTouch_iff_eq
  {d n : ℕ}
  {d n : ℕ}
  {a b : Site d} :
-- imply
  s(a, b) ∈ bondFinsetTouch d n ↔ ((hypercubicLattice d).Adj a b ∧ (a ∈ box d n ∨ b ∈ box d n)) := by
-- proof
  apply StatMech.IsingFK.hbx_mem_bondFinsetTouch_iff d n a b

/--
[hbx_mem_image_edgeIncl_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_mem_image_edgeIncl_iff_eq
  {d n : ℕ}
  {d m : ℕ}
  {a b : Site d} :
-- imply
  s(a, b) ∈ Finset.image (edgeIncl d m) (boxGraph d m).edgeFinset ↔ (a ∈ box d m ∧ b ∈ box d m ∧ (hypercubicLattice d).Adj a b) := by
-- proof
  apply StatMech.IsingFK.hbx_mem_image_edgeIncl_iff d m a b

/--
[hbx_touch_subset_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_touch_subset_image_eq
  {d n : ℕ}
  {d n : ℕ} :
-- imply
  bondFinsetTouch d n ⊆ Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset := by
-- proof
  apply StatMech.IsingFK.hbx_touch_subset_image d n

/--
[hbx_isingBond_latToBox_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_isingBond_latToBox_eq_eq
  {d n : ℕ}
  {d n : ℕ}
  {e : Sym2 (boxVerts d (n + 1))}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  isingBond (latToBox d n τ) e = bond (glue (plusField d) τ) (edgeIncl d (n + 1) e) := by
-- proof
  apply StatMech.IsingFK.hbx_isingBond_latToBox_eq d n τ e

/--
[hbx_edge_energy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_edge_energy_eq
  {d n : ℕ}
  {d n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  ∑ e ∈ (boxGraph d (n + 1)).edgeFinset, isingBond (latToBox d n τ) e = (∑ e ∈ bondFinsetTouch d n, bond (glue (plusField d) τ) e) + ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset) \ bondFinsetTouch d n).card := by
-- proof
  apply StatMech.IsingFK.hbx_edge_energy d n τ

/--
[hbx_fToB_bToF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_fToB_bToF_eq
  {d n : ℕ}
  {b : Bool} :
-- imply
  fToB (bToF b) = b := by
-- proof
  apply StatMech.IsingFK.hbx_fToB_bToF b

/--
[hbx_bToF_fToB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_bToF_fToB_eq
  {d n : ℕ}
  {a : Fin 2} :
-- imply
  bToF (fToB a) = a := by
-- proof
  apply StatMech.IsingFK.hbx_bToF_fToB a

/--
[hbx_boxBoundary_succ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_boxBoundary_succ_iff_eq
  {d n : ℕ}
  {d n : ℕ}
  {v : boxVerts d (n + 1)} :
-- imply
  boxBoundary d (n + 1) v ↔ (v : Site d) ∉ box d n := by
-- proof
  apply StatMech.IsingFK.hbx_boxBoundary_succ_iff d n v

/--
[hbx_sum_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_sum_reindex_eq
  {d n : ℕ}
  {d n : ℕ}
  {f : (boxVerts d (n + 1) → Fin 2) → ℝ}
-- given
  (hf : ∀ σ, ¬ BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ → f σ = 0) :
-- imply
  ∑ σ : boxVerts d (n + 1) → Fin 2, f σ = ∑ τ : {x // x ∈ box d n} → Bool, f (latToBox d n τ) := by
-- proof
  apply StatMech.IsingFK.hbx_sum_reindex d n f hf

/--
[hbx_fvWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_fvWeight_eq_eq
  {d n : ℕ}
  {d n : ℕ}
  {β : ℝ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ = Real.exp (β * ∑ e ∈ bondFinsetTouch d n, bond (glue (plusField d) τ) e) := by
-- proof
  apply StatMech.IsingFK.hbx_fvWeight_eq d n β τ

/--
[hbx_isingWiredWeight_latToBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_isingWiredWeight_latToBox_eq
  {d n : ℕ}
  {d n : ℕ}
  {β : ℝ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β (latToBox d n τ) = Real.exp (β * ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset) \ bondFinsetTouch d n).card) * fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ := by
-- proof
  apply StatMech.IsingFK.hbx_isingWiredWeight_latToBox d n β τ

/--
[hbx_isingWiredOnePoint_eq_fvMagnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_isingWiredOnePoint_eq_fvMagnetization_eq
  {d n : ℕ}
  {d n : ℕ}
  {β : ℝ} :
-- imply
  isingWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β (boxOrigin d (n + 1)) = fvMagnetization d β n := by
-- proof
  apply StatMech.IsingFK.hbx_isingWiredOnePoint_eq_fvMagnetization d n β

/--
[hbx_hisingBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_hisingBox_eq
  {d n : ℕ}
  {d : ℕ} :
-- imply
  ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)) := by
-- proof
  apply StatMech.IsingFK.hbx_hisingBox d

/--
[hbx_htransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_htransition_eq
  {d n : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) := by
-- proof
  apply StatMech.IsingFK.hbx_htransition d hd hFKsub hpc1

/--
[hbx_ising_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_ising_transition_eq
  {d n : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.IsingFK.hbx_ising_transition d hd hmag_nonneg hFKsub hpc0 hpc1

/--
[hbx_isingBetaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_isingBetaC_eq_eq
  {d n : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.IsingFK.hbx_isingBetaC_eq d hd hmag_nonneg hFKsub hpc0 hpc1

/--
[hbx_isingBetaC_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean)
-/
@[path]
private lemma hbx_isingBetaC_pos_eq
  {d n : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.IsingFK.hbx_isingBetaC_pos d hd hmag_nonneg hFKsub hpc0 hpc1


-- created on 2026-10-23
