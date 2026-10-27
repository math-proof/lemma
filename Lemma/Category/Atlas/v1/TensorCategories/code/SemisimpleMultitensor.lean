import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
open CategoryTheory MonoidalCategory CategoryTheory.Limits


namespace CategoryTheory

/--
[isSemisimpleObject_of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
lemma isSemisimpleObject_of_iso
  {C : Type u}
  [Category.{v} C]
  [HasZeroMorphisms C]
  {C}
  {X Y : C}
  {i : X ≅ Y}
-- given
  (h : IsSemisimpleObject C Y) :
-- imply
  IsSemisimpleObject C X := by
-- proof
  obtain ⟨n, f, hb, hsimp, ⟨iso⟩⟩ := h
  exact ⟨n, f, hb, hsimp, ⟨i ≪≫ iso⟩⟩

end CategoryTheory

namespace CategoryTheory

/--
[unit_isSemisimpleObject](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
lemma unit_isSemisimpleObject
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  [IsSemisimpleCategory C] :
-- imply
  IsSemisimpleObject C (𝟙_ C) :=
-- proof
  IsSemisimpleCategory.semisimple (𝟙_ C)

end CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
/--
[isSplitEpi_cokernel_π_of_isSplitMono_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
algebraically closed field, the `k`-dimension of `𝟙_ C ⟶ V ⊗ Vᘁ` equals the `k`-dimension of the
endomorphism algebra `V ⟶ V`. -/
lemma isSplitEpi_cokernel_π_of_isSplitMono_aux
  [Preadditive C] [Abelian C]
  {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] :
  IsSplitEpi (Limits.cokernel.π f) := by
  obtain ⟨⟨retraction, hretraction⟩⟩ := hf.exists_splitMono
  have hcomp : f ≫ (𝟙 Y - retraction ≫ f) = 0 := by
    simp [reassoc_of% hretraction]
  constructor
  refine ⟨⟨Limits.cokernel.desc f (𝟙 Y - retraction ≫ f) hcomp, ?_⟩⟩
  rw [← cancel_epi (Limits.cokernel.π f)]
  simp only [Limits.cokernel.π_desc_assoc, Category.comp_id]
  simp [Limits.cokernel.condition]

end CategoryTheory

namespace CategoryTheory

/--
[coevaluation_ne_zero_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
lemma coevaluation_ne_zero_of_simple
  [Preadditive C]
  [MonoidalPreadditive C]
  {V : C}
  [Simple V] :
-- imply
  η_ V (Vᘁ) ≠ 0 := by
-- proof
  intro h_zero
  have h_triangle := ExactPairing.evaluation_coevaluation' (X := V) (Y := Vᘁ)
  change ExactPairing.coevaluation' = (0 : 𝟙_ C ⟶ V ⊗ Vᘁ) at h_zero
  rw [h_zero, MonoidalPreadditive.zero_whiskerRight] at h_triangle
  simp at h_triangle
  apply id_nonzero V
  have h_lam_zero : (λ_ V).hom = 0 := by
    rw [← cancel_mono (ρ_ V).inv, Limits.zero_comp]; exact h_triangle.symm
  calc 𝟙 V = (λ_ V).inv ≫ (λ_ V).hom := by simp
    _ = (λ_ V).inv ≫ 0 := by rw [h_lam_zero]
    _ = 0 := by simp

end CategoryTheory

namespace CategoryTheory

/--
[evaluation_ne_zero_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
lemma evaluation_ne_zero_of_simple
  [Preadditive C]
  [MonoidalPreadditive C]
  {V : C}
  [Simple V] :
-- imply
  ε_ (Vᘁ) ((Vᘁ)ᘁ) ≠ 0 := by
-- proof
  intro h_eps_zero
  have h_triangle := ExactPairing.evaluation_coevaluation' (X := Vᘁ) (Y := (Vᘁ)ᘁ)
  change ExactPairing.evaluation' = (0 : (Vᘁ)ᘁ ⊗ Vᘁ ⟶ 𝟙_ C) at h_eps_zero
  rw [h_eps_zero, MonoidalPreadditive.whiskerLeft_zero] at h_triangle
  simp at h_triangle
  have h_lam_zero : (λ_ (Vᘁ)).hom = 0 := by
    rw [← cancel_mono (ρ_ (Vᘁ)).inv, Limits.zero_comp]; exact h_triangle.symm
  have h_id_Vd_zero : 𝟙 (Vᘁ) = 0 := by
    calc 𝟙 (Vᘁ) = (λ_ (Vᘁ)).inv ≫ (λ_ (Vᘁ)).hom := by simp
      _ = (λ_ (Vᘁ)).inv ≫ 0 := by rw [h_lam_zero]
      _ = 0 := by simp
  have h_eta_zero : η_ V (Vᘁ) = 0 := by
    calc η_ V (Vᘁ) = η_ V (Vᘁ) ≫ 𝟙 (V ⊗ Vᘁ) := by simp
      _ = η_ V (Vᘁ) ≫ (V ◁ 𝟙 (Vᘁ)) := by rw [whiskerLeft_id]
      _ = η_ V (Vᘁ) ≫ (V ◁ (0 : Vᘁ ⟶ Vᘁ)) := by rw [h_id_Vd_zero]
      _ = η_ V (Vᘁ) ≫ 0 := by rw [MonoidalPreadditive.whiskerLeft_zero]
      _ = 0 := by simp
  exact coevaluation_ne_zero_of_simple h_eta_zero
/-- Key technical step in Proposition 1.41.5: for any choice of double-dual isomorphism
`a : V ≅ (Vᘁ)ᘁ` on a simple object in a `k`-linear semisimple rigid category, the resulting left
quantum trace `tr_L(a)` is nonzero. -/
section Corollary_1_15_9

end CategoryTheory

namespace CategoryTheory

/--
[evaluation_ne_zero_of_nonzero_obj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
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

end CategoryTheory

namespace CategoryTheory

/--
[coevaluation_ne_zero_of_nonzero_obj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
lemma coevaluation_ne_zero_of_nonzero_obj
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
  η_ X Xᘁ ≠ 0 := by
-- proof
  intro h
  apply hX; rw [IsZero.iff_id_eq_zero]
  have zig := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [h] at zig
  simp [MonoidalPreadditive.zero_whiskerRight] at zig
  have hlam : (λ_ X).hom = 0 := by rw [← cancel_mono (ρ_ X).inv]; simp [zig]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

end CategoryTheory

/--
[isZero_tensor_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma isZero_tensor_left_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {A B : C}
-- given
  (h : IsZero A) :
-- imply
  IsZero (A ⊗ B) := by
-- proof
  apply CategoryTheory.isZero_tensor_left h

/--
[isZero_tensor_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma isZero_tensor_right_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {A B : C}
-- given
  (h : IsZero B) :
-- imply
  IsZero (A ⊗ B) := by
-- proof
  apply CategoryTheory.isZero_tensor_right h

/--
[whisker_unitor_calc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma whisker_unitor_calc_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {A B : C}
  {s : A ⟶ 𝟙_ C}
  {r : 𝟙_ C ⟶ B} :
-- imply
  (ρ_ A).inv ≫ A ◁ r ≫ s ▷ B ≫ (λ_ B).hom = s ≫ r := by
-- proof
  apply CategoryTheory.whisker_unitor_calc s r

/--
[unitComponent_tensor_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma unitComponent_tensor_zero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {n : ℕ}
  {f : Fin n → C}
  [HasBiproduct f]
  {i j : Fin n}
-- given
  (hiso : 𝟙_ C ≅ ⨁ f)
  (hsimp : ∀ i, Simple (f i))
  (hij : i ≠ j) :
-- imply
  IsZero (f i ⊗ f j) := by
-- proof
  apply CategoryTheory.unitComponent_tensor_zero f hiso hsimp hij

/--
[tensor_component_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma tensor_component_zero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {n : ℕ}
  {f : Fin n → C}
  [HasBiproduct f]
  {X Y : C}
  {i j k l : Fin n}
-- given
  (hiso : 𝟙_ C ≅ ⨁ f)
  (hsimp : ∀ i, Simple (f i))
  (hjk : j ≠ k) :
-- imply
  IsZero (componentObj f X i j ⊗ componentObj f Y k l) := by
-- proof
  apply CategoryTheory.tensor_component_zero f hiso hsimp X Y i j k l hjk

/--
[rightAdjointMate_unit_endo](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma rightAdjointMate_unit_endo_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  [RigidCategory C]
  {g : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  rightAdjointMate g = g := by
-- proof
  apply CategoryTheory.rightAdjointMate_unit_endo g

/--
[object_componentDecomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma object_componentDecomposition_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {n : ℕ}
  {f : Fin n → C}
  [HasBiproduct f]
  {X : C}
-- given
  (hiso : 𝟙_ C ≅ ⨁ f)
  (hsimp : ∀ i, Simple (f i)) :
-- imply
  ∃ (_ : HasBiproduct (componentFamily f X)), Nonempty (X ≅ ⨁ (componentFamily f X)) := by
-- proof
  apply CategoryTheory.object_componentDecomposition f hiso hsimp X

/--
[isSplitEpi_cokernel_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean)
-/
@[path]
private lemma isSplitEpi_cokernel__eq
  [Preadditive C]
  [Abelian C]
  {X Y : C}
  {f : X ⟶ Y}
  [hf : IsSplitMono f] :
-- imply
  IsSplitEpi (Limits.cokernel.π f) := by
-- proof
  apply CategoryTheory.isSplitEpi_cokernel_ f


-- created on 2026-10-23
