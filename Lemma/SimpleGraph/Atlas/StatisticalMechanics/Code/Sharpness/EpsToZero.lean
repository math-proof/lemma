import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.EpsToZero
open Filter Topology Finset SimpleGraph StatMech StatMech.Sharpness


/--
[set_susceptibility_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZero.lean)
-/
@[path]
private lemma set_susceptibility_sum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) := by
-- proof
  apply StatMech.Sharpness.set_susceptibility_sum_nonneg G β h hβ hh o

/--
[ghs_susceptibility_sum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZero.lean)
-/
@[path]
private lemma ghs_susceptibility_sum_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 < h) :
-- imply
  ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) ≤ 1 / (β * h) := by
-- proof
  apply StatMech.Sharpness.ghs_susceptibility_sum_bound G β h hβ hh o

/--
[eps_annular_bound_of_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZero.lean)
-/
@[path]
private lemma eps_annular_bound_of_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : ℕ → ℝ}
  {h : ℝ}
  {n k : ℕ}
-- given
  (hMono : Monotone M)
  (hh : 0 < h)
  (_hk : k ≤ n) :
-- imply
  0 ≤ (1 / h) * (M n - M (n - k)) := by
-- proof
  apply StatMech.Sharpness.eps_annular_bound_of_mono G hMono hh n k _hk

/--
[set_annularDiff_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZero.lean)
-/
@[path]
private lemma set_annularDiff_tendsto_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : ℕ → ℝ}
  {L : ℝ}
  {k : ℕ}
-- given
  (hM : Tendsto M atTop (𝓝 L)) :
-- imply
  Tendsto (fun n : ℕ => M n - M (n - k)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Sharpness.set_annularDiff_tendsto_zero G M hM k

/--
[set_eps_to_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZero.lean)
-/
@[path]
private lemma set_eps_to_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ε tail M : ℕ → ℝ}
  {L h : ℝ}
-- given
  (_hh : 0 < h)
  (hpos : ∀ n, 0 ≤ ε n)
  (hsplit : ∀ k n, k ≤ n → ε n ≤ tail k + (1 / h) * (M n - M (n - k)))
  (htail : Tendsto tail atTop (𝓝 0))
  (hM : Tendsto M atTop (𝓝 L)) :
-- imply
  Tendsto ε atTop (𝓝 0) := by
-- proof
  apply StatMech.Sharpness.set_eps_to_zero G ε tail M _hh hpos hsplit htail hM


-- created on 2026-10-23
