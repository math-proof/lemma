import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RHorseNumberFubini
open scoped BigOperators
open MetaMathlibExt


/--
[rHorseNumber_eq_stirlingFirst_sum_fubini](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorseNumber_eq_stirlingFirst_sum_fubini_eq
  {n r : ℕ}
-- given
  (hrn : r ≤ n) :
-- imply
  ((∑ k ∈ Finset.range (n + 1),
    Nat.card
    { f : Fin n → Fin k //
    Function.Surjective f ∧
    ∀ i j : Fin r, i < j →
    f (Fin.castLE hrn i) < f (Fin.castLE hrn j) }) : ℚ) =
    (1 / (Nat.factorial r : ℚ)) *
    ∑ j ∈ Finset.range (r + 1),
    (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
    (fubiniNumber (n - j) : ℚ) := by
-- proof
  apply MetaMathlibExt.rHorseNumber_eq_stirlingFirst_sum_fubini n r hrn


-- created on 2026-10-20
