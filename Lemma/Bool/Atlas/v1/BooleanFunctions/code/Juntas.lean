import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Juntas
open BooleanFourier


namespace BooleanFourier

/--
[influence_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Juntas.lean)
-/
@[path]
lemma influence_nonneg
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  0 ≤ influence f i := by
-- proof
  unfold influence
  positivity

end BooleanFourier

namespace BooleanFourier

/--
[high_influence_count_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Juntas.lean)
-/
@[path]
lemma high_influence_count_le
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {τ : ℝ}
-- given
  (hτ : 0 < τ) :
-- imply
  ((highInfluenceCoords f τ).card : ℝ) ≤ totalInfluence f / τ := by
-- proof
  set J := highInfluenceCoords f τ
  have hJ : ∀ i ∈ J, τ ≤ influence f i := by
    intro i hi
    simp only [J, highInfluenceCoords, Finset.mem_filter] at hi
    exact hi.2
  have h1 : (J.card : ℝ) * τ ≤ ∑ i ∈ J, influence f i := by
    have hsm : J.card • τ ≤ ∑ i ∈ J, influence f i :=
      Finset.card_nsmul_le_sum J (fun i => influence f i) τ (fun i hi => hJ i hi)
    rwa [nsmul_eq_mul] at hsm
  have h2 : ∑ i ∈ J, influence f i ≤ totalInfluence f := by
    exact Finset.sum_le_univ_sum_of_nonneg (fun i => influence_nonneg f i)
  rw [le_div_iff₀ hτ]
  linarith

end BooleanFourier


-- created on 2026-10-23
