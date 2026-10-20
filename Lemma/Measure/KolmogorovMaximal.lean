import Mathlib
import sympy.Basic
import sympy.atlas.Probability.KolmogorovMaximal
open Finset BigOperators
open MathlibExt.Probability.KolmogorovMaximal


/--
[kolmogorov_maximal_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/KolmogorovMaximal.lean)
-/
@[path]
private lemma kolmogorov_maximal_inequality_eq
  [DecidableEq α] [Fintype α] [Nonempty α]
  {n : ℕ}
  {p X : Fin n → α → ℝ}
  {lam : ℝ}
-- given
  (hp_nonneg : ∀ i a, 0 ≤ p i a)
  (hp_sum : ∀ i, ∑ a : α, p i a = 1)
  (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0)
  (hlam : 0 < lam) :
-- imply
  (∑ ω ∈ Finset.univ.filter
    (fun ω : Fin n → α =>
    ∃ i : Fin n,
    |∑ j ∈ Finset.univ.filter
    (fun j : Fin n => j ≤ i), X j (ω j)| ≥ lam),
    ∏ i : Fin n, p i (ω i))
    ≤ (∑ i : Fin n, ∑ a : α, p i a * (X i a) ^ 2) / lam ^ 2 := by
-- proof
  apply MathlibExt.Probability.KolmogorovMaximal.kolmogorov_maximal_inequality p hp_nonneg hp_sum X h_mean lam hlam


-- created on 2026-10-20
