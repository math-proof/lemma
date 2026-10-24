import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section23
open CategoryTheory AlgebraicTopology TensorProduct in DirectLimitCharacterization
open TensorProduct
open CategoryTheory CategoryTheory.Limits
open TensorProduct Module Module.DirectLimit
open Module.DirectLimit


namespace DirectLimitCharacterization

/--
[directLimit_lift_bijective_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section23.lean)
-/
@[path]
lemma directLimit_lift_bijective_iff
  [Ring R] :
-- imply
  Function.Bijective (lift R ι G f g Hg) ↔ ((∀ x : L, ∃ i, ∃ xᵢ : G i, g i xᵢ = x) ∧ (∀ i (xᵢ : G i), g i xᵢ = 0 → ∃ j, ∃ (hij : i ≤ j), f i j hij xᵢ = 0)) := by
-- proof
  constructor
  · intro ⟨hinj, hsurj⟩
    exact ⟨fun x => by
      obtain ⟨z, hz⟩ := hsurj x
      obtain ⟨i, xi, hxi⟩ := exists_of z
      exact ⟨i, xi, by rw [← hz, ← hxi, lift_of]⟩,
      fun i xi hgi => by
        have hof : of R ι G f i xi = 0 := by
          apply hinj; rw [lift_of, hgi, map_zero]
        exact of.zero_exact hof⟩
  · intro ⟨hsurj, hker⟩
    refine ⟨fun z w hzw => ?_, fun x => ?_⟩
    · suffices h : ∀ z : Module.DirectLimit G f, lift R ι G f g Hg z = 0 → z = 0 by
      have : lift R ι G f g Hg (z - w) = 0 := by rw [map_sub, sub_eq_zero.mpr hzw]
      have := h _ this
      rwa [sub_eq_zero] at this
      intro z hz
      obtain ⟨i, xi, rfl⟩ := exists_of z
      rw [lift_of] at hz
      obtain ⟨j, hij, hfij⟩ := hker i xi hz
      rw [show of R ι G f i xi = of R ι G f j (f i j hij xi) from of_f.symm, hfij, map_zero]
    · obtain ⟨i, xi, hxi⟩ := hsurj x
      exact ⟨of R ι G f i xi, by rw [lift_of, hxi]⟩
end DirectLimitCharacterization
namespace AlgebraicTopologyI
open CategoryTheory AlgebraicTopology TensorProduct



-- created on 2026-10-23
