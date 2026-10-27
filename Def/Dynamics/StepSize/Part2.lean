import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorem.Dynamics.StepSize
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

-- anchor times: t 0 = 0, t (n+1) = min {k | T n ≤ ∑ i ∈ [t n, k), α i} (rl: `Anchors.t`)
noncomputable def t : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.find (anc.exists_le n (t n))


-- aggregated steps β n = ∑ i ∈ [t n, t (n+1)), α i (rl: `Anchors.β`)
noncomputable def β (n : ℕ) : ℝ :=
  ∑ i ∈ Ico (anc.t n) (anc.t (n + 1)), α i

end Anchors

-- α (t n) ≤ C β n² for some C ≥ 0 (rl: `StochasticApproximation.SufficientlySparse`)
def SufficientlySparse {α : ℕ → ℝ} (anc : Anchors α) : Prop :=
  ∃ C, 0 ≤ C ∧ ∀ n, α (anc.t n) ≤ C * anc.β n ^ 2

-- inverse-polynomial step sizes n ↦ (n + n₀)^(-ν) (rl: `StochasticApproximation.inv_poly`)
noncomputable def inv_poly (ν : ℝ) (n₀ : ℕ) : ℝ → ℝ :=
  fun n => (n + n₀) ^ (-ν)

