import Mathlib
import sympy.Basic
import sympy.atlas.Probability.StrassenCoupling
open Finset
open MathlibExt.Probability.StrassenCouplingWanted


/--
[forall_isUpperSet_sum_le_iff_exists_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/StrassenCoupling.lean)
-/
@[path]
private lemma forall_isUpperSet_sum_le_iff_exists_coupling_eq
  [Fintype α] [PartialOrder α]
  {p q : α → ℝ}
-- given
  (hp_nonneg : ∀ x, 0 ≤ p x)
  (hq_nonneg : ∀ x, 0 ≤ q x)
  (hsum : ∑ x : α, p x = ∑ x : α, q x) :
-- imply
  (∀ U : Finset α, IsUpperSet U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x) ↔
    ∃ π : α → α → ℝ,
    (∀ x y, 0 ≤ π x y) ∧
    (∀ x, ∑ y : α, π x y = p x) ∧
    (∀ y, ∑ x : α, π x y = q y) ∧
    (∀ x y, ¬ x ≤ y → π x y = 0) := by
-- proof
  apply MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling p q hp_nonneg hq_nonneg hsum

/--
[strassen_coupling_finite_poset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/StrassenCoupling.lean)
-/
@[path]
private lemma strassen_coupling_finite_poset_eq
  [Fintype α] [PartialOrder α] [DecidableEq α] [DecidableLE α]
  {p q : α → ℝ}
-- given
  (hp_nonneg : ∀ x, 0 ≤ p x)
  (hq_nonneg : ∀ x, 0 ≤ q x)
  (hp_sum : ∑ x : α, p x = 1)
  (hq_sum : ∑ x : α, q x = 1) :
-- imply
  (∀ U : Finset α, IsUpperSet U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x) ↔
    ∃ π : α → α → ℝ,
    (∀ x y, 0 ≤ π x y) ∧
    (∀ x, ∑ y : α, π x y = p x) ∧
    (∀ y, ∑ x : α, π x y = q y) ∧
    (∀ x y, ¬ x ≤ y → π x y = 0) := by
-- proof
  apply MathlibExt.Probability.StrassenCouplingWanted.strassen_coupling_finite_poset p q hp_nonneg hq_nonneg hp_sum hq_sum


-- created on 2026-10-20
