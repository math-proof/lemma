module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Instance.Dynamics.StepSize
open Finset Filter

/-!
# Step-size schedules for stochastic approximation

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/StepSize.lean`.

* `RobbinsMonro α`: the Robbins–Monro conditions on a step-size sequence `α : ℕ → ℝ`
  (positive, `∑ α = ∞`, `∑ α² < ∞`). A `Prop`-valued class, following `RowStochastic`.
* `Anchors α`: an antitone Robbins–Monro sequence `α` together with a second Robbins–Monro
  sequence `T` of anchor lengths. From it one builds the anchor times `Anchors.t`
  (`t 0 = 0`, `t (n+1)` = the first `k` with `T n ≤ ∑ i ∈ [t n, k), α i`) and the aggregated steps
  `Anchors.β n = ∑ i ∈ [t n, t (n+1)), α i`.
* `SufficientlySparse anc`: `α (t n) ≤ C β n²` for some `C ≥ 0`.
* `inv_poly ν n₀ n = (n + n₀)^(-ν)`.
-/

public section


namespace Anchors

variable {α : ℕ → ℝ} (anc : Anchors α)

-- the partial sums of α beyond tm eventually exceed T m (rl: `Anchors.exists_le`)
theorem exists_le (m tm : ℕ) : ∃ k, anc.le m tm k := by
  have h := (tendsto_add_atTop_iff_nat tm).2 anc.hα.sum
  obtain ⟨k, hk⟩ := (h.eventually_ge_atTop (anc.T m + ∑ i ∈ range tm, α i)).exists
  refine ⟨k + tm, ?_⟩
  have e : ∑ i ∈ range (k + tm), α i = ∑ i ∈ range tm, α i + ∑ i ∈ Ico tm (k + tm), α i := by
    rw [range_eq_Ico, range_eq_Ico, sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_add_left _ _)]
  simp only [le]
  linarith

end Anchors
