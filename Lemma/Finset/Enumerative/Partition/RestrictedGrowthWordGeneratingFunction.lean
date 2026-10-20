import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.RestrictedGrowthWordGeneratingFunction
open MetaMathlibExt


/--
[restricted_growth_word_monomial_generating_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RestrictedGrowthWordGeneratingFunction.lean)
-/
@[path]
private lemma restricted_growth_word_monomial_generating_function_eq
  {k : ℕ} :
-- imply
  ((fun d : Fin k →₀ ℕ =>
    (Nat.card {
    u : Fin (k + d.sum fun _ m => m) → Fin k //
    (∀ i, (u i : ℕ) = 0 ∨
    ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) ∧
    ∀ a, Nat.card {i : Fin (k + d.sum fun _ m => m) // u i = a} = d a + 1
    } : ℚ)) : MvPowerSeries (Fin k) ℚ) =
    (∏ j : Fin k,
    (1 - ∑ i ∈ Finset.Iic j, MvPowerSeries.X i)⁻¹ : MvPowerSeries (Fin k) ℚ) := by
-- proof
  apply MetaMathlibExt.restricted_growth_word_monomial_generating_function k


-- created on 2026-10-20
