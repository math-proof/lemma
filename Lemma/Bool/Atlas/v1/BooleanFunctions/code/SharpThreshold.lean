import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.SharpThreshold
open BooleanFourier
open Finset


namespace BooleanFourier

/--
[influence_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/SharpThreshold.lean)
-/
@[path]
lemma influence_le_one
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  influence f i ≤ 1 := by
-- proof
  unfold influence
  rw [div_le_one (by positivity : (2 : ℝ) ^ n > 0)]
  have hle : (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card ≤
    Finset.univ.card :=
    Finset.card_filter_le _ _
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hle
  exact_mod_cast hle

end BooleanFourier

namespace BooleanFourier

/--
[totalInfluence_le_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/SharpThreshold.lean)
-/
@[path]
lemma totalInfluence_le_n
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f ≤ (n : ℝ) := by
-- proof
  show ∑ i : Fin n, influence f i ≤ (n : ℝ)
  calc ∑ i : Fin n, influence f i
    ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => influence_le_one f i)
    _ = (n : ℝ) := by simp [Finset.card_univ, Fintype.card_fin]

end BooleanFourier


-- created on 2026-10-23
