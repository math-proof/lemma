/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/StrassenCoupling.lean -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

section
open Finset

namespace MathlibExt.Probability.StrassenCouplingWanted

/-!
# Finite Strassen stochastic domination
-/

/-- `U` is upward-closed / an upper set: `x ∈ U` and `x ≤ y` implies `y ∈ U`. -/
def IsUpperSet {α : Type*} [Preorder α] (U : Finset α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ U → x ≤ y → y ∈ U

/-- upper set of the sub-poset carried by `s`. -/
private def UpOn {α : Type*} [Preorder α] (s U : Finset α) : Prop :=
  U ⊆ s ∧ ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ s → x ≤ y → y ∈ U

/-- support-count of `p` inside `s`. -/
private noncomputable def sp {α : Type*} (s : Finset α) (p : α → ℝ) : ℕ :=
  (s.filter (fun x => p x ≠ 0)).card

/-- combined measure. -/
private noncomputable def M {α : Type*} (s : Finset α) (p q : α → ℝ) : ℕ :=
  s.card * (2 * s.card + 1) + (sp s p + sp s q)

/-- The hypotheses of the carrier-form coupling problem. -/
private def Hyps {α : Type*} [PartialOrder α] (s : Finset α) (p q : α → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧
  (∀ x, x ∉ s → p x = 0) ∧ (∀ x, x ∉ s → q x = 0) ∧
  (∑ x ∈ s, p x = ∑ x ∈ s, q x) ∧
  (∀ U, UpOn s U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x)

/-- The conclusion: a coupling supported on `{x ≤ y}` and inside `s × s`. -/
private def Concl {α : Type*} [Preorder α] (s : Finset α) (p q : α → ℝ) : Prop :=
  ∃ π : α → α → ℝ, (∀ x y, 0 ≤ π x y) ∧
    (∀ x, ∑ y ∈ s, π x y = p x) ∧ (∀ y, ∑ x ∈ s, π x y = q y) ∧
    (∀ x y, ¬ x ≤ y → π x y = 0) ∧ (∀ x y, π x y ≠ 0 → x ∈ s ∧ y ∈ s)
end MathlibExt.Probability.StrassenCouplingWanted
