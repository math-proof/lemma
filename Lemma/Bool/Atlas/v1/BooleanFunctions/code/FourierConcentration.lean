import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Juntas
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Juntas
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.MonotoneFourier
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Theorems
import sympy.atlas.v1.Atlas.BooleanFunctions.code.InfluenceFourier
import sympy.atlas.v1.Atlas.BooleanFunctions.code.MonotoneFourier
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Talagrand
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Theorems
open Finset BigOperators


namespace BooleanFourier

/--
[fourierInfluence_eq_influenceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma fourierInfluence_eq_influenceReal
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {i : Fin n} :
-- imply
  fourierInfluence f i = influenceReal f i := by
-- proof
  rw [influenceReal_eq_sum_fourierCoeff_sq]
  unfold fourierInfluence
  rw [← Finset.sum_filter]

end BooleanFourier

namespace BooleanFourier

/--
[fourierInfluence_liftPM_eq_influence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma fourierInfluence_liftPM_eq_influence
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  fourierInfluence (liftPM f) i = influence f i := by
-- proof
  rw [fourierInfluence_eq_influenceReal]
  have : liftPM f = fun x => boolToReal (f x) := rfl
  rw [this, ← influence_eq_influenceReal]

end BooleanFourier

namespace BooleanFourier

/--
[influence_lt_of_not_mem_highInfluenceCoords](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma influence_lt_of_not_mem_highInfluenceCoords
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {τ : ℝ}
  {i : Fin n}
-- given
  (hi : i ∉ highInfluenceCoords f τ) :
-- imply
  influence f i < τ := by
-- proof
  simp only [highInfluenceCoords, Finset.mem_filter, Finset.mem_univ, true_and,
    not_le] at hi
  exact hi

end BooleanFourier

namespace BooleanFourier

/--
[fourierInfluence_lt_of_not_mem_J](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma fourierInfluence_lt_of_not_mem_J
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {τ : ℝ}
  {i : Fin n}
-- given
  (hi : i ∉ highInfluenceCoords f τ) :
-- imply
  fourierInfluence (liftPM f) i < τ := by
-- proof
  rw [fourierInfluence_liftPM_eq_influence]
  exact influence_lt_of_not_mem_highInfluenceCoords f τ i hi

end BooleanFourier

namespace BooleanFourier

/--
[fourierCoeff_sq_lt_of_not_subset_J](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma fourierCoeff_sq_lt_of_not_subset_J
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {τ : ℝ}
  {S : Finset (Fin n)}
-- given
  (hS : ¬(S ⊆ highInfluenceCoords f τ)) :
-- imply
  fourierCoeff (liftPM f) S ^ 2 < τ := by
-- proof
  rw [Finset.not_subset] at hS
  obtain ⟨i, hi_S, hi_nJ⟩ := hS
  calc fourierCoeff (liftPM f) S ^ 2
    ≤ fourierInfluence (liftPM f) i :=
      fourierCoeff_sq_le_fourierInfluence (liftPM f) S i hi_S
    _ < τ := fourierInfluence_lt_of_not_mem_J f τ i hi_nJ

end BooleanFourier

namespace BooleanFourier

/--
[log_inv_pos_of_tau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma log_inv_pos_of_tau
  {τ : ℝ}
-- given
  (hτ0 : 0 < τ)
  (hτ1 : τ < 1) :
-- imply
  Real.log (1 / τ) > 0 := by
-- proof
  rw [Real.log_div (by linarith : (1 : ℝ) ≠ 0) (ne_of_gt hτ0)]
  simp only [Real.log_one, zero_sub]
  exact neg_pos.mpr (Real.log_neg hτ0 hτ1)

end BooleanFourier

namespace BooleanFourier

/--
[fourierCoeff_sq_le_one_of_liftPM](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierConcentration.lean)
-/
@[path]
lemma fourierCoeff_sq_le_one_of_liftPM
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {S : Finset (Fin n)} :
-- imply
  fourierCoeff (liftPM f) S ^ 2 ≤ 1 := by
-- proof
  have hpars : ∑ T : Finset (Fin n), fourierCoeff (liftPM f) T ^ 2 = 1 := by
    have : liftPM f = fun x => boolToReal (f x) := rfl
    rw [this]
    exact parseval_signed f
  have hS_mem : S ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ S
  have h_le := Finset.single_le_sum (f := fun T => fourierCoeff (liftPM f) T ^ 2)
    (fun T _ => sq_nonneg _) hS_mem
  linarith

end BooleanFourier


-- created on 2026-10-23
