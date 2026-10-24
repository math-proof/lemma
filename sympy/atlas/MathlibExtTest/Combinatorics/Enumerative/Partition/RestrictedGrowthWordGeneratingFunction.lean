/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/RestrictedGrowthWordGeneratingFunction.lean -/


import sympy.atlas.Combinatorics.Enumerative.Partition.RestrictedGrowthWordGeneratingFunction
import Lemma.Finset.Enumerative.Partition.RestrictedGrowthWordGeneratingFunction

namespace MetaMathlibExt

-- Specialize the restricted-growth-word product formula to a one-letter alphabet.
example :
    ((fun d : Fin 1 →₀ ℕ =>
      (Nat.card {
        u : Fin (1 + d.sum fun _ m => m) → Fin 1 //
          (∀ i, (u i : ℕ) = 0 ∨
            ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) ∧
          ∀ a, Nat.card {i : Fin (1 + d.sum fun _ m => m) // u i = a} = d a + 1
      } : ℚ)) : MvPowerSeries (Fin 1) ℚ) =
      (∏ j : Fin 1,
        (1 - ∑ i ∈ Finset.Iic j, MvPowerSeries.X i)⁻¹ : MvPowerSeries (Fin 1) ℚ) :=
  restricted_growth_word_monomial_generating_function 1

end MetaMathlibExt
