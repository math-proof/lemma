import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.CRecursiveExponentialGrowth
open MetaMathlibExt


/--
[exists_norm_lt_pow_of_isSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CRecursiveExponentialGrowth.lean)
-/
@[path]
private lemma exists_norm_lt_pow_of_isSolution_eq
  {E : LinearRecurrence ℂ}
  {t : ℕ → ℂ}
-- given
  (h : E.IsSolution t) :
-- imply
  ∃ g : ℤ, 1 ≤ g ∧ ∀ n : ℕ, ‖t n‖ < ((g : ℝ) ^ (n + 1)) := by
-- proof
  apply MetaMathlibExt.exists_norm_lt_pow_of_isSolution E t h

/--
[c_recursive_exponential_growth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CRecursiveExponentialGrowth.lean)
-/
@[path]
private lemma c_recursive_exponential_growth_bound_eq
  {t : ℕ → ℂ}
-- given
  (h : ∃ k : ℕ, 1 ≤ k ∧ ∃ c : Fin k → ℂ, ∀ n : ℕ, t (n + k) = ∑ i : Fin k, c i * t (n + i.val)) :
-- imply
  ∃ g : ℤ, 1 ≤ g ∧ ∀ n : ℕ, ‖t n‖ < ((g : ℝ) ^ (n + 1)) := by
-- proof
  apply MetaMathlibExt.c_recursive_exponential_growth_bound t h


-- created on 2026-10-20
