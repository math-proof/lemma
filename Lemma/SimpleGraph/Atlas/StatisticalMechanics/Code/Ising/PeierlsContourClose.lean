import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.PeierlsContourClose
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[pcc_contourLen_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_contourLen_empty_eq
  {d : ℕ}
  {B : Finset (Sym2 (Site d))} :
-- imply
  contourLen (∅ : Set (Site d)) B = 0 := by
-- proof
  apply StatMech.Ising.pcc_contourLen_empty B

/--
[pcc_empty_mem_clusterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_empty_mem_clusterFamily_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (∅ : Finset (Site d)) ∈ clusterFamily (d := d) n := by
-- proof
  apply StatMech.Ising.pcc_empty_mem_clusterFamily n

/--
[pcc_one_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_one_le_sum_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  (1 : ℝ) ≤ ∑ K ∈ clusterFamily (d := d) n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.pcc_one_le_sum n β

/--
[pcc_not_contourCountBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_not_contourCountBound_eq
  {d : ℕ} :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → ¬ ContourCountBound d n β := by
-- proof
  apply StatMech.Ising.pcc_not_contourCountBound

/--
[pcc_mem_originClusterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_mem_originClusterFamily_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)} :
-- imply
  K ∈ originClusterFamily (d := d) n ↔ K ∈ clusterFamily (d := d) n ∧ origin d ∈ K := by
-- proof
  apply StatMech.Ising.pcc_mem_originClusterFamily

/--
[pcc_minusClusterFinset_mem_originFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_minusClusterFinset_mem_originFamily_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  minusClusterFinset τ ho ∈ originClusterFamily (d := d) n := by
-- proof
  apply StatMech.Ising.pcc_minusClusterFinset_mem_originFamily τ ho

/--
[pcc_probOriginMinus_le_sum_probContour_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_probOriginMinus_le_sum_probContour_origin_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ ∑ K ∈ originClusterFamily (d := d) n, probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
-- proof
  apply StatMech.Ising.pcc_probOriginMinus_le_sum_probContour_origin n β

/--
[pcc_probOriginMinus_le_sum_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_probOriginMinus_le_sum_origin_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ ∑ K ∈ originClusterFamily (d := d) n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.pcc_probOriginMinus_le_sum_origin n β

/--
[pcc_rayS_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_rayS_zero_eq
  {d : ℕ}
  {c : Fin d} :
-- imply
  pcc_rayS c 0 = origin d := by
-- proof
  apply StatMech.Ising.pcc_rayS_zero c

/--
[pcc_rayS_mem_box_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_rayS_mem_box_le_eq
  {d : ℕ}
  {c : Fin d}
  {j m : ℕ}
-- given
  (h : j ≤ m) :
-- imply
  pcc_rayS c j ∈ box d m := by
-- proof
  apply StatMech.Ising.pcc_rayS_mem_box_le c j m h

/--
[pcc_rayS_succ_not_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_rayS_succ_not_mem_box_eq
  {d : ℕ}
  {c : Fin d}
  {n : ℕ} :
-- imply
  pcc_rayS c (n+1) ∉ box d n := by
-- proof
  apply StatMech.Ising.pcc_rayS_succ_not_mem_box c n

/--
[pcc_rayS_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_rayS_adj_eq
  {d : ℕ}
  {c : Fin d}
  {j : ℕ} :
-- imply
  (hypercubicLattice d).Adj (pcc_rayS c j) (pcc_rayS c (j+1)) := by
-- proof
  apply StatMech.Ising.pcc_rayS_adj c j

/--
[pcc_rayEdge_mem_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_rayEdge_mem_bondFinsetTouch_eq
  {d : ℕ}
  {n : ℕ}
  {c : Fin d}
  {j : ℕ}
-- given
  (hj : j ≤ n) :
-- imply
  s(pcc_rayS c j, pcc_rayS c (j+1)) ∈ bondFinsetTouch d n := by
-- proof
  apply StatMech.Ising.pcc_rayEdge_mem_bondFinsetTouch n c j hj

/--
[pcc_one_le_contourLen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_one_le_contourLen_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hKbox : (↑K : Set (Site d)) ⊆ box d n)
  (hoK : origin d ∈ K) :
-- imply
  1 ≤ contourLen (↑K) (bondFinsetTouch d n) := by
-- proof
  apply StatMech.Ising.pcc_one_le_contourLen hd hKbox hoK

/--
[pcc_peierlsContourBound_of_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_peierlsContourBound_of_origin_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hCount : OriginContourCountBound d n β) :
-- imply
  PeierlsContourBound d n β := by
-- proof
  apply StatMech.Ising.pcc_peierlsContourBound_of_origin n β hCount

/--
[pcc_peierls_long_range_order_of_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean)
-/
@[path]
private lemma pcc_peierls_long_range_order_of_origin_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hCount : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → OriginContourCountBound d n β) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.pcc_peierls_long_range_order_of_origin hd hCount


-- created on 2026-10-23
