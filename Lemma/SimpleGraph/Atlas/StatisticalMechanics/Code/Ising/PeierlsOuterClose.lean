import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterClose.Part2
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[mem_holeFreeClusterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma mem_holeFreeClusterFamily_eq
  {n : ℕ}
  {K : Finset (Site 2)} :
-- imply
  K ∈ holeFreeClusterFamily n ↔ K ∈ clusterFamily (d := 2) n ∧ IsHoleFreeBoxCluster n K := by
-- proof
  apply StatMech.Ising.mem_holeFreeClusterFamily

/--
[holeFreeClusterFamily_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeClusterFamily_subset_box_eq
  {n : ℕ}
  {K : Finset (Site 2)}
-- given
  (hK : K ∈ holeFreeClusterFamily n) :
-- imply
  (↑K : Set (Site 2)) ⊆ box 2 n := by
-- proof
  apply StatMech.Ising.holeFreeClusterFamily_subset_box hK

/--
[outerUnionBound_le_sum_probContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma outerUnionBound_le_sum_probContour_eq
  {n : ℕ}
  {β : ℝ}
-- given
  (hWind : OuterContourWinding n) :
-- imply
  probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ ∑ K ∈ holeFreeClusterFamily n, probContour (↑K) (plusField 2) n (bondFinsetTouch 2 n) β := by
-- proof
  apply StatMech.Ising.outerUnionBound_le_sum_probContour n β hWind

/--
[outerUnionBound_le_sum_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma outerUnionBound_le_sum_exp_eq
  {n : ℕ}
  {β : ℝ}
-- given
  (hWind : OuterContourWinding n) :
-- imply
  probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ ∑ K ∈ holeFreeClusterFamily n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ)) := by
-- proof
  apply StatMech.Ising.outerUnionBound_le_sum_exp n β hWind

/--
[mem_holeFreeAtLen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma mem_holeFreeAtLen_eq
  {n ℓ : ℕ}
  {K : Finset (Site 2)} :
-- imply
  K ∈ holeFreeAtLen n ℓ ↔ K ∈ holeFreeClusterFamily n ∧ contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ := by
-- proof
  apply StatMech.Ising.mem_holeFreeAtLen

/--
[holeFree_circuit_encoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFree_circuit_encoding_eq
  {n ℓ : ℕ}
  {K : Finset (Site 2)}
-- given
  (hK : K ∈ holeFreeAtLen n ℓ) :
-- imply
  ∃ (j : ℕ), j < ℓ ∧ axisVertex 2 j ∈ anchorFinset ℓ ∧ ∃ W : (hypercubicLattice 2).Walk (axisVertex 2 j) (axisVertex 2 j), W.length = ℓ ∧ dualWalkContour ⟨axisVertex 2 j, W⟩ = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
-- proof
  apply StatMech.Ising.holeFree_circuit_encoding hK

/--
[holeFreeAtLen_mem_connFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeAtLen_mem_connFamily_eq
  {n ℓ : ℕ}
  {K : Finset (Site 2)}
-- given
  (hK : K ∈ holeFreeAtLen n ℓ) :
-- imply
  K ∈ connClusterFamily (d := 2) n := by
-- proof
  apply StatMech.Ising.holeFreeAtLen_mem_connFamily hK

/--
[holeFreeAtLen_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeAtLen_card_le_eq
  {n ℓ : ℕ} :
-- imply
  (holeFreeAtLen n ℓ).card ≤ 2 * ℓ * (2 * 2) ^ ℓ := by
-- proof
  apply StatMech.Ising.holeFreeAtLen_card_le n ℓ

/--
[holeFreeClusterFamily_contourLen_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeClusterFamily_contourLen_lt_eq
  {n : ℕ}
  {K : Finset (Site 2)}
-- given
  (hK : K ∈ holeFreeClusterFamily n) :
-- imply
  contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) < 2 * 2 * (boxFinset 2 n).card + 1 := by
-- proof
  apply StatMech.Ising.holeFreeClusterFamily_contourLen_lt hK

/--
[holeFreeSum_eq_lengthSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeSum_eq_lengthSum_eq
  {n : ℕ}
  {β : ℝ} :
-- imply
  ∑ K ∈ holeFreeClusterFamily n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ)) = ∑ ℓ ∈ Finset.range (2 * 2 * (boxFinset 2 n).card + 1), ((holeFreeAtLen n ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
-- proof
  apply StatMech.Ising.holeFreeSum_eq_lengthSum n β

/--
[holeFreeAtLen_card_le_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeAtLen_card_le_real_eq
  {n ℓ : ℕ} :
-- imply
  ((holeFreeAtLen n ℓ).card : ℝ) ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by
-- proof
  apply StatMech.Ising.holeFreeAtLen_card_le_real n ℓ

/--
[holeFreeSum_le_twoPeierls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma holeFreeSum_le_twoPeierls_eq
  {n : ℕ}
  {β : ℝ}
-- given
  (hx : peierlsRatio 2 β < 1) :
-- imply
  ∑ K ∈ holeFreeClusterFamily n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ)) ≤ twoPeierlsBound 2 β := by
-- proof
  apply StatMech.Ising.holeFreeSum_le_twoPeierls n β hx

/--
[outerProbOriginMinus_le_two_peierls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma outerProbOriginMinus_le_two_peierls_eq
  {n : ℕ}
  {β : ℝ}
-- given
  (hx : peierlsRatio 2 β < 1)
  (hWind : OuterContourWinding n) :
-- imply
  probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β := by
-- proof
  apply StatMech.Ising.outerProbOriginMinus_le_two_peierls n β hx hWind

/--
[peierls_long_range_order_of_outerWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma peierls_long_range_order_of_outerWinding_eq
-- given
  (hWind : ∀ n : ℕ, OuterContourWinding n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order_of_outerWinding hWind

/--
[singletonOrigin_isHoleFreeBoxCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma singletonOrigin_isHoleFreeBoxCluster_eq
  {n : ℕ}
-- given
  (hd : 1 ≤ 2) :
-- imply
  IsHoleFreeBoxCluster n ({origin 2} : Finset (Site 2)) := by
-- proof
  apply StatMech.Ising.singletonOrigin_isHoleFreeBoxCluster hd n

/--
[singletonOrigin_mem_holeFreeClusterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean)
-/
@[path]
private lemma singletonOrigin_mem_holeFreeClusterFamily_eq
  {n : ℕ} :
-- imply
  ({origin 2} : Finset (Site 2)) ∈ holeFreeClusterFamily n := by
-- proof
  apply StatMech.Ising.singletonOrigin_mem_holeFreeClusterFamily n


-- created on 2026-10-23
