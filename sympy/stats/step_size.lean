import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

open Finset Filter

-- Robbins–Monro step sizes: positive, divergent sum, square-summable (rl: `StochasticApproximation.RobbinsMonro`)
class RobbinsMonro (α : ℕ → ℝ) : Prop where
  pos : ∀ n, 0 < α n
  sum : Tendsto (fun n => ∑ k ∈ range n, α k) atTop atTop
  sqsum : Summable fun n => α n ^ 2

-- anchors for an antitone Robbins–Monro sequence α (rl: `StochasticApproximation.Anchors`)
structure Anchors (α : ℕ → ℝ) where
  hα : RobbinsMonro α
  hα_mono : Antitone α
  T : ℕ → ℝ
  hT : RobbinsMonro T

namespace Anchors

variable {α : ℕ → ℝ} (anc : Anchors α)

-- the predicate `T m ≤ ∑ i ∈ [tm, k), α i` on k (rl: `Anchors.le`)
def le (m tm : ℕ) : ℕ → Prop :=
  fun k => anc.T m ≤ ∑ i ∈ Ico tm k, α i

noncomputable instance (m tm : ℕ) : DecidablePred (anc.le m tm) :=
  Classical.decPred _

-- the partial sums of α beyond tm eventually exceed T m (rl: `Anchors.exists_le`)
lemma exists_le (m tm : ℕ) : ∃ k, anc.le m tm k := by
  have h := (tendsto_add_atTop_iff_nat tm).2 anc.hα.sum
  obtain ⟨k, hk⟩ := (h.eventually_ge_atTop (anc.T m + ∑ i ∈ range tm, α i)).exists
  refine ⟨k + tm, ?_⟩
  have e : ∑ i ∈ range (k + tm), α i = ∑ i ∈ range tm, α i + ∑ i ∈ Ico tm (k + tm), α i := by
    rw [range_eq_Ico, range_eq_Ico, sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_add_left _ _)]
  simp only [le]
  linarith

-- anchor times: t 0 = 0, t (n+1) = min {k | T n ≤ ∑ i ∈ [t n, k), α i} (rl: `Anchors.t`)
noncomputable def t : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.find (anc.exists_le n (t n))

lemma t_zero : anc.t 0 = 0 := rfl

lemma t_succ (n : ℕ) : anc.t (n + 1) = Nat.find (anc.exists_le n (anc.t n)) := rfl

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