import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.TraceNonzero
open CategoryTheory MonoidalCategory Category TensorCategories


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
variable (k : Type w) [Field k] [IsAlgClosed k]
variable [Preadditive C] [Linear k C] [Abelian C]
variable [MonoidalPreadditive C] [MonoidalLinear k C]
/--
[isSplitEpi_cokernel_π_of_isSplitMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean)
-/
@[path]
the same `k`-dimension as the endomorphism algebra of `V`. -/
lemma isSplitEpi_cokernel_π_of_isSplitMono
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

end TensorCategories

namespace TensorCategories

/--
[finrank_ge_two_of_mono_and_nonzero_cokernel_desc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean)
-/
@[path]
lemma finrank_ge_two_of_mono_and_nonzero_cokernel_desc
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [IsAlgClosed k]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
  [SemisimpleCategory C]
  [Simple (𝟙_ C)]
  {X : C}
  {f : 𝟙_ C ⟶ X}
  {g' : Limits.cokernel f ⟶ 𝟙_ C}
  [FiniteDimensional k (𝟙_ C ⟶ X)]
-- given
  (_hf_mono : Mono f)
  (_hg' : g' ≠ 0) :
-- imply
  Module.finrank k (𝟙_ C ⟶ X) ≥ 2 := by
-- proof
  haveI : IsSplitMono f := SemisimpleCategory.mono_isSplitMono f
  haveI : IsSplitEpi (Limits.cokernel.π f) := isSplitEpi_cokernel_π_of_isSplitMono f
  obtain ⟨⟨σ_π, hσ_π⟩⟩ := (inferInstance : IsSplitEpi (Limits.cokernel.π f)).exists_splitEpi
  haveI : Epi g' := epi_of_nonzero_to_simple _hg'
  haveI : IsSplitEpi g' := SemisimpleCategory.epi_isSplitEpi g'
  obtain ⟨⟨ι_g', hι_g'⟩⟩ := (inferInstance : IsSplitEpi g').exists_splitEpi
  have hι_ne_zero : ι_g' ≠ 0 := by
    intro h; rw [h, Limits.zero_comp] at hι_g'; exact id_nonzero (𝟙_ C) hι_g'.symm
  let hh : 𝟙_ C ⟶ X := ι_g' ≫ σ_π
  have hhh_comp_π : hh ≫ Limits.cokernel.π f = ι_g' := by
    simp only [hh, Category.assoc, hσ_π, Category.comp_id]
  have hh_ne_zero : hh ≠ 0 := by
    intro h; rw [h, Limits.zero_comp] at hhh_comp_π; exact hι_ne_zero hhh_comp_π.symm
  have hf_ne_zero : f ≠ 0 := by
    intro hf0; rw [hf0] at _hf_mono
    have : (𝟙 (𝟙_ C)) ≫ (0 : 𝟙_ C ⟶ X) = (0 : 𝟙_ C ⟶ 𝟙_ C) ≫ (0 : 𝟙_ C ⟶ X) := by simp
    exact id_nonzero (𝟙_ C) (_hf_mono.right_cancellation _ _ this)
  have h_lin_indep : LinearIndependent k ![f, hh] := by
    rw [linearIndependent_fin2]
    refine ⟨hh_ne_zero, fun a ha => ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
    have step1 : (a • hh) ≫ Limits.cokernel.π f = a • ι_g' := by
      rw [Linear.smul_comp, hhh_comp_π]
    have step2 : f ≫ Limits.cokernel.π f = 0 := Limits.cokernel.condition f
    have step3 : a • ι_g' = 0 := by rw [← step1, ha, step2]
    have ha0 : a = 0 := by
      by_contra ha_ne
      exact hι_ne_zero
        (by rw [← one_smul k ι_g', ← inv_mul_cancel₀ ha_ne, mul_smul, step3, smul_zero])
    rw [ha0, zero_smul] at ha
    exact hf_ne_zero ha.symm
  have := h_lin_indep.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  omega

end TensorCategories

namespace TensorCategories

/--
[composition_nonzero_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean)
-/
@[path]
lemma composition_nonzero_of_finrank_one
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [IsAlgClosed k]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
  [SemisimpleCategory C]
  [Simple (𝟙_ C)]
  {X : C}
  {f : 𝟙_ C ⟶ X}
  {g : X ⟶ 𝟙_ C}
  [FiniteDimensional k (𝟙_ C ⟶ X)]
-- given
  (hfin : Module.finrank k (𝟙_ C ⟶ X) = 1)
  (hf : f ≠ 0)
  (hg : g ≠ 0) :
-- imply
  f ≫ g ≠ 0 := by
-- proof
  intro h_comp_zero
  have hf_mono : Mono f := mono_of_nonzero_from_simple hf
  let g' := Limits.cokernel.desc f g h_comp_zero
  have hπg' : Limits.cokernel.π f ≫ g' = g := Limits.cokernel.π_desc f g h_comp_zero
  have hg' : g' ≠ 0 := by
    intro hg'_zero
    rw [hg'_zero, Limits.comp_zero] at hπg'
    exact hg hπg'.symm
  have h_ge_2 := finrank_ge_two_of_mono_and_nonzero_cokernel_desc k f hf_mono g' hg'
  omega

end TensorCategories

namespace TensorCategories

/--
[coevaluation_ne_zero_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean)
-/
@[path]
lemma coevaluation_ne_zero_of_simple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [IsAlgClosed k]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
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

end TensorCategories

namespace TensorCategories

/--
[evaluation_ne_zero_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean)
-/
@[path]
lemma evaluation_ne_zero_of_simple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [IsAlgClosed k]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
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

end TensorCategories

/--
[isSplitEpi_cokernel_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean)
-/
@[path]
private lemma isSplitEpi_cokernel__eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [IsAlgClosed k]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
  {X Y : C}
  {f : X ⟶ Y}
  [hf : IsSplitMono f] :
-- imply
  IsSplitEpi (Limits.cokernel.π f) := by
-- proof
  apply TensorCategories.isSplitEpi_cokernel_ k f


-- created on 2026-10-23
