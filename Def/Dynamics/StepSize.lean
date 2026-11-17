module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Structure.Dynamics.StepSize

@[expose] public section

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


namespace Anchors

variable {α : ℕ → ℝ} (anc : Anchors α)

-- the predicate `T m ≤ ∑ i ∈ [tm, k), α i` on k (rl: `Anchors.le`)
def le (m tm : ℕ) : ℕ → Prop :=
  fun k => anc.T m ≤ ∑ i ∈ Ico tm k, α i

end Anchors
