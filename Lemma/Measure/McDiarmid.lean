import Mathlib
import sympy.Basic
import sympy.atlas.Probability.McDiarmid
open Finset BigOperators
open MathlibExt.Probability.McDiarmid


/--
[mcdiarmid_one_sided_finite_iid_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/McDiarmid.lean)
-/
@[path]
private lemma mcdiarmid_one_sided_finite_iid_general_eq
  [Fintype α] [Nonempty α]
  {n : ℕ}
  {p : α → ℝ}
  {f : (Fin n → α) → ℝ}
  {c : Fin n → ℝ}
  {t : ℝ}
-- given
  (hp_nonneg : ∀ a, 0 ≤ p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hc_nonneg : ∀ i, 0 ≤ c i)
  (hc_pos : 0 < ∑ i : Fin n, c i ^ 2)
  (ht : 0 < t)
  (hbd : ∀ (i : Fin n) (x y : Fin n → α), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
-- imply
  let mu : ℝ := by
-- proof
  apply MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid_general p hp_nonneg hp_sum f c hc_nonneg hc_pos t ht hbd

/--
[mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/McDiarmid.lean)
-/
@[path]
private lemma mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero_eq
  [Fintype α] [Nonempty α]
  {n : ℕ}
  {p : α → ℝ}
  {f : (Fin n → α) → ℝ}
  {c : Fin n → ℝ}
  {t : ℝ}
-- given
  (hp_nonneg : ∀ a, 0 ≤ p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hc_nonneg : ∀ i, 0 ≤ c i)
  (hc_zero : ∑ i : Fin n, c i ^ 2 = 0)
  (ht : 0 < t)
  (hbd : ∀ (i : Fin n) (x y : Fin n → α), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
-- imply
  let mu : ℝ := by
-- proof
  apply MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero p hp_nonneg hp_sum f c hc_nonneg hc_zero t ht hbd

/--
[mcdiarmid_one_sided_finite_iid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/McDiarmid.lean)
-/
@[path]
private lemma mcdiarmid_one_sided_finite_iid_eq
  [Fintype α] [DecidableEq α] [Nonempty α]
  {n : ℕ}
  {p : α → ℝ}
  {f : (Fin n → α) → ℝ}
  {c : Fin n → ℝ}
  {t : ℝ}
-- given
  (hp_nonneg : ∀ a, 0 ≤ p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hc_nonneg : ∀ i, 0 ≤ c i)
  (ht : 0 < t)
  (hbd : ∀ (i : Fin n) (x y : Fin n → α), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
-- imply
  let mu : ℝ := by
-- proof
  apply MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid p hp_nonneg hp_sum f c hc_nonneg t ht hbd


-- created on 2026-10-20
