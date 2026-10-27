import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.EvalCoeval
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits TensorCategories


namespace TensorCategories

/--
[evaluation_ne_zero_of_nonzero_obj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/EvalCoeval.lean)
-/
@[path]
lemma evaluation_ne_zero_of_nonzero_obj
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [RightRigidCategory C]
  [MonoidalPreadditive C]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  ε_ X Xᘁ ≠ 0 := by
-- proof
  intro h
  apply hX; rw [IsZero.iff_id_eq_zero]
  have zig := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [h] at zig
  simp [MonoidalPreadditive.whiskerLeft_zero] at zig
  have hlam : (λ_ X).hom = 0 := by rw [← cancel_mono (ρ_ X).inv]; simp [zig]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

end TensorCategories


-- created on 2026-10-23
