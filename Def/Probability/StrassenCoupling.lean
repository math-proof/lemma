/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/StrassenCoupling.lean -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

@[expose] public section

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
def UpOn {α : Type*} [Preorder α] (s U : Finset α) : Prop :=
  U ⊆ s ∧ ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ s → x ≤ y → y ∈ U

/-- support-count of `p` inside `s`. -/
noncomputable def sp {α : Type*} (s : Finset α) (p : α → ℝ) : ℕ :=
  (s.filter (fun x => p x ≠ 0)).card

/-- combined measure. -/
noncomputable def M {α : Type*} (s : Finset α) (p q : α → ℝ) : ℕ :=
  s.card * (2 * s.card + 1) + (sp s p + sp s q)

/-- The hypotheses of the carrier-form coupling problem. -/
def Hyps {α : Type*} [PartialOrder α] (s : Finset α) (p q : α → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧
  (∀ x, x ∉ s → p x = 0) ∧ (∀ x, x ∉ s → q x = 0) ∧
  (∑ x ∈ s, p x = ∑ x ∈ s, q x) ∧
  (∀ U, UpOn s U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x)

/-- The conclusion: a coupling supported on `{x ≤ y}` and inside `s × s`. -/
def Concl {α : Type*} [Preorder α] (s : Finset α) (p q : α → ℝ) : Prop :=
  ∃ π : α → α → ℝ, (∀ x y, 0 ≤ π x y) ∧
    (∀ x, ∑ y ∈ s, π x y = p x) ∧ (∀ y, ∑ x ∈ s, π x y = q y) ∧
    (∀ x y, ¬ x ≤ y → π x y = 0) ∧ (∀ x y, π x y ≠ 0 → x ∈ s ∧ y ∈ s)

end MathlibExt.Probability.StrassenCouplingWanted
end
