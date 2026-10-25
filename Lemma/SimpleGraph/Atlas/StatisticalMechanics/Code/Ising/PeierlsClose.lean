import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[pcl_contourEnergy_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_contourEnergy_eq_pow_eq
  {d : ℕ}
  {β : ℝ}
  {ℓ : ℕ} :
-- imply
  Real.exp (-(2 * β) * (ℓ : ℝ)) = (Real.exp (-(2 * β))) ^ ℓ := by
-- proof
  apply StatMech.Ising.pcl_contourEnergy_eq_pow β ℓ

/--
[pcl_summand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_summand_eq_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {ℓ : ℕ} :
-- imply
  (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (Real.exp (-(2 * β))) ^ ℓ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
-- proof
  apply StatMech.Ising.pcl_summand_eq d β ℓ

/--
[pcl_summable_peierlsSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_summable_peierlsSummand_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
-- given
  (hx : peierlsRatio d β < 1) :
-- imply
  Summable (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
-- proof
  apply StatMech.Ising.pcl_summable_peierlsSummand d β hx

/--
[pcl_lengthSum_le_peierlsBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_lengthSum_le_peierlsBound_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {T : Finset ℕ}
-- given
  (hx : peierlsRatio d β < 1) :
-- imply
  ∑ ℓ ∈ T, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) ≤ peierlsBound d β := by
-- proof
  apply StatMech.Ising.pcl_lengthSum_le_peierlsBound d β hx T

/--
[pcl_clusterSum_le_lengthSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_clusterSum_le_lengthSum_eq
  {d : ℕ}
  [DecidableEq α]
  {S : Finset α}
  {len : α → ℕ}
  {c : ℝ}
  {count : ℕ → ℝ}
-- given
  (hc : 0 ≤ c)
  (hcount : ∀ ℓ, ((S.filter (fun K => len K = ℓ)).card : ℝ) ≤ count ℓ) :
-- imply
  ∑ K ∈ S, c ^ (len K) ≤ ∑ ℓ ∈ S.image len, count ℓ * c ^ ℓ := by
-- proof
  apply StatMech.Ising.pcl_clusterSum_le_lengthSum S len c hc count hcount

/--
[pcl_connectedContourCountBound_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_connectedContourCountBound_of_count_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hx : peierlsRatio d β < 1)
  (hCount : ConnectedContourCount d n) :
-- imply
  ConnectedContourCountBound d n β := by
-- proof
  apply StatMech.Ising.pcl_connectedContourCountBound_of_count n β hx hCount

/--
[pcl_exists_beta_ratio_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_exists_beta_ratio_lt_one_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → peierlsRatio d β < 1 := by
-- proof
  apply StatMech.Ising.pcl_exists_beta_ratio_lt_one d

/--
[pcl_peierls_long_range_order_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean)
-/
@[path]
private lemma pcl_peierls_long_range_order_of_count_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hCount : ∀ n : ℕ, ConnectedContourCount d n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.pcl_peierls_long_range_order_of_count hd hCount


-- created on 2026-10-23
