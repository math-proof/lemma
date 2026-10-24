import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Talagrand
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[fourierCoeff_sq_le_fourierInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Talagrand.lean)
-/
@[path]
lemma fourierCoeff_sq_le_fourierInfluence
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)}
  {i : Fin n}
-- given
  (hi : i ∈ S) :
-- imply
  fourierCoeff f S ^ 2 ≤ fourierInfluence f i := by
-- proof
  simp only [fourierInfluence]
  calc fourierCoeff f S ^ 2
    = if i ∈ S then fourierCoeff f S ^ 2 else 0 := by simp [hi]
    _ ≤ ∑ T : Finset (Fin n), if i ∈ T then fourierCoeff f T ^ 2 else 0 := by
      apply Finset.single_le_sum
        (f := fun T => if i ∈ T then fourierCoeff f T ^ 2 else 0)
      · intro T _; split_ifs <;> positivity
      · exact Finset.mem_univ S

end BooleanFourier

namespace BooleanFourier

/--
[fourierCoeff_sq_le_avg_fourierInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Talagrand.lean)
-/
@[path]
lemma fourierCoeff_sq_le_avg_fourierInfluence
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)}
-- given
  (hS : S.Nonempty) :
-- imply
  fourierCoeff f S ^ 2 ≤ (1 / (S.card : ℝ)) * ∑ i ∈ S, fourierInfluence f i := by
-- proof
  have hcard_pos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcard_pos, mul_comm]
  have h : ∀ i ∈ S, fourierCoeff f S ^ 2 ≤ fourierInfluence f i :=
    fun i hi => fourierCoeff_sq_le_fourierInfluence f S i hi
  calc (S.card : ℝ) * fourierCoeff f S ^ 2
    = ∑ _i ∈ S, fourierCoeff f S ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ S, fourierInfluence f i := Finset.sum_le_sum h

end BooleanFourier


-- created on 2026-10-23
