import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.EvalCoevalArg
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits TensorCategories


namespace TensorCategories

/--
[isZero_dualTensor_tensor_of_isZero_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/EvalCoevalArg.lean)
-/
@[path]
lemma isZero_dualTensor_tensor_of_isZero_tensor
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {X Y : C}
-- given
  (h : IsZero (X ⊗ Y)) :
-- imply
  IsZero (((Xᘁ : C) ⊗ X) ⊗ Y) := by
-- proof
  haveI : (tensorLeft (Xᘁ : C)).PreservesZeroMorphisms :=
    ⟨fun _ _ => MonoidalPreadditive.whiskerLeft_zero⟩
  have h1 : IsZero ((Xᘁ : C) ⊗ (X ⊗ Y)) := (tensorLeft _).map_isZero h
  exact h1.of_iso (α_ Xᘁ X Y)

end TensorCategories

namespace TensorCategories

/--
[isZero_or_isZero_of_tensorObj_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/EvalCoevalArg.lean)
-/
@[path]
lemma isZero_or_isZero_of_tensorObj_isZero
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [Simple (𝟙_ C)]
  {X Y : C}
-- given
  (h : IsZero (X ⊗ Y)) :
-- imply
  IsZero X ∨ IsZero Y := by
-- proof
  by_contra hne
  push Not at hne
  obtain ⟨hX, hY⟩ := hne
  have h_dual : IsZero (((Xᘁ : C) ⊗ X) ⊗ Y) :=
    isZero_dualTensor_tensor_of_isZero_tensor X Y h
  have hε_whisk : ε_ X (Xᘁ : C) ▷ Y = 0 := h_dual.eq_of_src _ _
  have hε_ne : ε_ X (Xᘁ : C) ≠ 0 := evaluation_ne_zero_of_nonzero_obj X hX
  haveI hε_epi : Epi (ε_ X (Xᘁ : C)) := epi_of_nonzero_to_simple hε_ne
  have adj := tensorRightAdjunction Y (HasRightDual.rightDual Y)
  haveI := adj.leftAdjoint_preservesColimits
  haveI : (tensorRight Y).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  haveI : Epi (ε_ X (Xᘁ : C) ▷ Y) := (tensorRight Y).map_epi _
  have hUnit_Y_zero : IsZero ((𝟙_ C) ⊗ Y) := by
    rw [IsZero.iff_id_eq_zero]
    have hsrc : (ε_ X (Xᘁ : C) ▷ Y) ≫ (𝟙 ((𝟙_ C) ⊗ Y)) = 0 := by
      rw [hε_whisk]; simp
    exact (cancel_epi (ε_ X (Xᘁ : C) ▷ Y)).mp (by rw [hsrc, comp_zero])
  exact hY (hUnit_Y_zero.of_iso (λ_ Y).symm)

end TensorCategories


-- created on 2026-10-23
