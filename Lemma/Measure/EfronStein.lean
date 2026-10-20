import Mathlib
import sympy.Basic
import sympy.atlas.Probability.EfronStein
open Finset BigOperators
open MathlibExt.Probability.EfronStein


/--
[efron_stein_finite_iid_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/EfronStein.lean)
-/
@[path]
private lemma efron_stein_finite_iid_general_eq
  [Fintype α] [Nonempty α]
  {n : ℕ}
  {p : α → ℝ}
  {f : (Fin n → α) → ℝ}
-- given
  (hp_nonneg : ∀ a, 0 ≤ p a)
  (hp_sum : ∑ a : α, p a = 1) :
-- imply
  let μ : ℝ := by
-- proof
  apply MathlibExt.Probability.EfronStein.efron_stein_finite_iid_general p hp_nonneg hp_sum f

/--
[efron_stein_finite_iid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/EfronStein.lean)
-/
@[path]
private lemma efron_stein_finite_iid_eq
  [Fintype α] [DecidableEq α] [Nonempty α]
  {n : ℕ}
  {p : α → ℝ}
  {f : (Fin n → α) → ℝ}
-- given
  (hp_nonneg : ∀ a, 0 ≤ p a)
  (hp_sum : ∑ a : α, p a = 1) :
-- imply
  let μ : ℝ := by
-- proof
  apply MathlibExt.Probability.EfronStein.efron_stein_finite_iid p hp_nonneg hp_sum f


-- created on 2026-10-20
