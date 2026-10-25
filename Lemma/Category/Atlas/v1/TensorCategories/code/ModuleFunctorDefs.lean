import Mathlib
import sympy.Basic
import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
open CategoryTheory CategoryTheory.ModuleFunctorHom
open Category MonoidalCategory LeftModCat


namespace CategoryTheory

/--
[moduleCat_action_split_mono_of_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleCat_action_split_mono_of_exact
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [ExactModuleCategory.ActionRightExact C M]
  {P : C}
  [Projective P]
  {A B : M}
  {f : A ⟶ B}
-- given
  (hf : Mono f) :
-- imply
  ∃ (r : P ⊗ᵐ B ⟶ P ⊗ᵐ A), (P ◁ᵐ f) ≫ r = 𝟙 (P ⊗ᵐ A) := by
-- proof
  haveI := hf
  have sm := ExactModuleCategory.action_projective_split_mono P f
  exact ⟨sm.retraction, sm.id⟩

end CategoryTheory

namespace CategoryTheory

/--
[moduleAction_reflects_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleAction_reflects_mono
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [Projective (𝟙_ C)]
  {N : Type u₃}
  [Category.{v₃} N]
  [LeftModuleCategory C N]
  {A B : N}
  {g : A ⟶ B}
-- given
  (h : ∀ (P : C), Projective P → Mono (P ◁ᵐ g)) :
-- imply
  Mono g := by
-- proof
  haveI hunit : Mono ((𝟙_ C) ◁ᵐ g) := h (𝟙_ C) inferInstance
  have hnat := LeftModuleCategory.actLeftUnitor_naturality (C := C) (M := N) g
  have hf : g = (actℓ_ A).inv ≫ ((𝟙_ C) ◁ᵐ g) ≫ (actℓ_ B).hom := by
    rw [← hnat.symm, Iso.inv_hom_id_assoc]
  rw [hf]
  exact mono_comp _ _

end CategoryTheory

namespace CategoryTheory

/--
[moduleAction_reflects_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleAction_reflects_epi
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [Projective (𝟙_ C)]
  {N : Type u₃}
  [Category.{v₃} N]
  [LeftModuleCategory C N]
  {A B : N}
  {g : A ⟶ B}
-- given
  (h : ∀ (P : C), Projective P → Epi (P ◁ᵐ g)) :
-- imply
  Epi g := by
-- proof
  haveI hunit : Epi ((𝟙_ C) ◁ᵐ g) := h (𝟙_ C) inferInstance
  have hnat := LeftModuleCategory.actLeftUnitor_naturality (C := C) (M := N) g
  have hf : g = (actℓ_ A).inv ≫ ((𝟙_ C) ◁ᵐ g) ≫ (actℓ_ B).hom := by
    rw [← hnat.symm, Iso.inv_hom_id_assoc]
  rw [hf]
  exact epi_comp _ _

end CategoryTheory

namespace CategoryTheory

/--
[moduleCat_action_reflects_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleCat_action_reflects_mono
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [Projective (𝟙_ C)]
  {N : Type u₃}
  [Category.{v₃} N]
  [LeftModuleCategory C N]
  {A B : N}
  {g : A ⟶ B}
-- given
  (h : ∀ (P : C), Projective P → Mono (P ◁ᵐ g)) :
-- imply
  Mono g :=
-- proof
  moduleAction_reflects_mono g h

end CategoryTheory

namespace CategoryTheory

/--
[moduleCat_splitEpi_of_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleCat_splitEpi_of_projective
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {A B : M}
  {e : A ⟶ B}
-- given
  (he : Epi e)
  (hB : Projective B) :
-- imply
  ∃ (s : B ⟶ A), s ≫ e = 𝟙 B := by
-- proof
  haveI := he
  haveI := hB
  exact ⟨Projective.factorThru (𝟙 B) e, Projective.factorThru_comp (𝟙 B) e⟩

end CategoryTheory

namespace CategoryTheory

/--
[moduleCat_action_reflects_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleCat_action_reflects_epi
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [Projective (𝟙_ C)]
  {N : Type u₃}
  [Category.{v₃} N]
  [LeftModuleCategory C N]
  {A B : N}
  {g : A ⟶ B}
-- given
  (h : ∀ (P : C), Projective P → Epi (P ◁ᵐ g)) :
-- imply
  Epi g :=
-- proof
  moduleAction_reflects_epi g h

end CategoryTheory

namespace CategoryTheory

/--
[moduleCat_action_preserves_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleCat_action_preserves_epi
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [ExactModuleCategory.BiexactAction C M]
  {P : C}
  {A B : M}
  {f : A ⟶ B}
-- given
  (hf : Epi f) :
-- imply
  Epi (P ◁ᵐ f) := by
-- proof
  haveI := hf
  exact ExactModuleCategory.actWhiskerLeft_preserves_epi P f

end CategoryTheory

namespace CategoryTheory

/--
[moduleFunctorExactBetweenExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma moduleFunctorExactBetweenExact
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [Projective (𝟙_ C)]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [ExactModuleCategory.ActionRightExact C M]
  [ExactModuleCategory.BiexactAction C M]
  {N : Type u₃}
  [Category.{v₃} N]
  [LeftModuleCategory C N]
  {F : ModuleFunctor C M N} :
-- imply
  ModuleFunctorIsExact F where preserves_mono :=
-- proof
  fun {A B} f hf => by
    apply moduleCat_action_reflects_mono (C := C)
    intro P hP
    haveI := hP
    obtain ⟨r, hfr⟩ := moduleCat_action_split_mono_of_exact (C := C) P f hf
    have hFsplit : F.toFunctor.map (P ◁ᵐ f) ≫ F.toFunctor.map r =
      𝟙 (F.toFunctor.obj (P ⊗ᵐ A)) := by
      rw [← F.toFunctor.map_comp, hfr, F.toFunctor.map_id]
    have hnat := F.strIso_natural (𝟙 P) f
    simp at hnat
    have eq1 : P ◁ᵐ F.toFunctor.map f =
      (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by
      rw [← cancel_epi (F.strIso P A).hom, hnat]; simp
    let s := (F.strIso P B).inv ≫ F.toFunctor.map r ≫ (F.strIso P A).hom
    have hsplit : (P ◁ᵐ F.toFunctor.map f) ≫ s = 𝟙 _ := by
      calc (P ◁ᵐ F.toFunctor.map f) ≫ s
        = ((F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom) ≫
          ((F.strIso P B).inv ≫ F.toFunctor.map r ≫ (F.strIso P A).hom) := by rw [eq1]
        _ = (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫
          ((F.strIso P B).hom ≫ (F.strIso P B).inv) ≫
          F.toFunctor.map r ≫ (F.strIso P A).hom := by simp only [assoc]
        _ = (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫
          F.toFunctor.map r ≫ (F.strIso P A).hom := by
            rw [(F.strIso P B).hom_inv_id]; simp only [id_comp]
        _ = (F.strIso P A).inv ≫ (F.toFunctor.map (P ◁ᵐ f) ≫ F.toFunctor.map r) ≫
          (F.strIso P A).hom := by simp only [assoc]
        _ = (F.strIso P A).inv ≫ 𝟙 _ ≫ (F.strIso P A).hom := by rw [hFsplit]
        _ = 𝟙 _ := by simp
    constructor
    intro Z g h hgh
    have h1 : (g ≫ (P ◁ᵐ F.toFunctor.map f)) ≫ s = g := by rw [assoc, hsplit, comp_id]
    have h2 : (h ≫ (P ◁ᵐ F.toFunctor.map f)) ≫ s = h := by rw [assoc, hsplit, comp_id]
    rw [← h1, ← h2, hgh]
    preserves_epi := fun {A B} f hf => by
      apply moduleCat_action_reflects_epi (C := C)
      intro P hP
      haveI := hP
      have hPB : Projective (P ⊗ᵐ B) := ExactModuleCategory.action_preserves_projective P B
      have hPf : Epi (P ◁ᵐ f) := moduleCat_action_preserves_epi (C := C) P f hf
      obtain ⟨t, hft⟩ := moduleCat_splitEpi_of_projective (C := C) (P ◁ᵐ f) hPf hPB
      have hFsplit : F.toFunctor.map t ≫ F.toFunctor.map (P ◁ᵐ f) =
        𝟙 (F.toFunctor.obj (P ⊗ᵐ B)) := by
        rw [← F.toFunctor.map_comp, hft, F.toFunctor.map_id]
      have hnat := F.strIso_natural (𝟙 P) f
      simp at hnat
      have eq1 : P ◁ᵐ F.toFunctor.map f =
        (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by
        rw [← cancel_epi (F.strIso P A).hom, hnat]; simp
      let sec := (F.strIso P B).inv ≫ F.toFunctor.map t ≫ (F.strIso P A).hom
      have hsplit : sec ≫ (P ◁ᵐ F.toFunctor.map f) = 𝟙 _ := by
        calc sec ≫ (P ◁ᵐ F.toFunctor.map f)
          = ((F.strIso P B).inv ≫ F.toFunctor.map t ≫ (F.strIso P A).hom) ≫
            ((F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom) := by
              rw [eq1]
          _ = (F.strIso P B).inv ≫ F.toFunctor.map t ≫
            ((F.strIso P A).hom ≫ (F.strIso P A).inv) ≫
            F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by simp only [assoc]
          _ = (F.strIso P B).inv ≫ F.toFunctor.map t ≫
            F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by
              rw [(F.strIso P A).hom_inv_id]; simp only [id_comp]
          _ = (F.strIso P B).inv ≫ (F.toFunctor.map t ≫ F.toFunctor.map (P ◁ᵐ f)) ≫
            (F.strIso P B).hom := by simp only [assoc]
          _ = (F.strIso P B).inv ≫ 𝟙 _ ≫ (F.strIso P B).hom := by rw [hFsplit]
          _ = 𝟙 _ := by simp
      constructor
      intro Z g h hgh
      have h1 : sec ≫ (P ◁ᵐ F.toFunctor.map f) ≫ g = g := by rw [← assoc, hsplit, id_comp]
      have h2 : sec ≫ (P ◁ᵐ F.toFunctor.map f) ≫ h = h := by rw [← assoc, hsplit, id_comp]
      rw [← h1, ← h2, hgh]

end CategoryTheory

namespace CategoryTheory

/--
[proposition_2_7_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma proposition_2_7_8
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [FiniteMultitensorBase C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [ExactModuleInfra C M]
  {N : Type u₃}
  [Category.{v₃} N]
  [LeftModuleCategory C N]
  {F : ModuleFunctor C M N} :
-- imply
  ModuleFunctorIsExact F :=
-- proof
  moduleFunctorExactBetweenExact F

end CategoryTheory

namespace CategoryTheory

/--
[compositionBifunctorBiexact_postcomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma compositionBifunctorBiexact_postcomp
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [Projective (𝟙_ C)]
  {M₁ : Type u₂}
  [Category.{v₂} M₁]
  [ExactModuleCategory C M₁]
  {M₂ : Type u₃}
  [Category.{v₃} M₂]
  [ExactModuleCategory C M₂]
  [Abelian M₂]
  [ExactModuleCategory.ActionRightExact C M₂]
  [ExactModuleCategory.BiexactAction C M₂]
  {M₃ : Type u₄}
  [Category.{v₄} M₃]
  [ExactModuleCategory C M₃]
  {G : ModuleFunctor C M₂ M₃}
  {F₁ F₂ : ModuleFunctor C M₁ M₂}
  {η : F₁ ⟶ F₂} :
-- imply
  (∀ (A : M₁), Mono (η.natTrans.app A) → Mono (G.toFunctor.map (η.natTrans.app A))) ∧ (∀ (A : M₁), Epi (η.natTrans.app A) → Epi (G.toFunctor.map (η.natTrans.app A))) :=
-- proof
  let hG := moduleFunctorExactBetweenExact G
  ⟨fun A hm => hG.preserves_mono (η.natTrans.app A) hm,
    fun A he => hG.preserves_epi (η.natTrans.app A) he⟩

end CategoryTheory

namespace CategoryTheory

/--
[compositionBifunctorBiexact_precomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
lemma compositionBifunctorBiexact_precomp
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M₁ : Type u₂}
  [Category.{v₂} M₁]
  [ExactModuleCategory C M₁]
  {M₂ : Type u₃}
  [Category.{v₃} M₂]
  [ExactModuleCategory C M₂]
  [Abelian M₂]
  {M₃ : Type u₄}
  [Category.{v₄} M₃]
  [ExactModuleCategory C M₃]
  {F : ModuleFunctor C M₁ M₂}
  {G₁ G₂ : ModuleFunctor C M₂ M₃}
  {η : G₁ ⟶ G₂} :
-- imply
  ((∀ (B : M₂), Mono (η.natTrans.app B)) → ∀ (A : M₁), Mono (η.natTrans.app (F.toFunctor.obj A))) ∧ ((∀ (B : M₂), Epi (η.natTrans.app B)) → ∀ (A : M₁), Epi (η.natTrans.app (F.toFunctor.obj A))) :=
-- proof
  ⟨fun hm A => hm (F.toFunctor.obj A), fun he A => he (F.toFunctor.obj A)⟩
/-- Every module functor between exact module categories admits a left adjoint at the level
of underlying functors. -/

end CategoryTheory

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean)
-/
@[path]
private lemma ext_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {F G : ModuleFunctor C M N}
  {η θ : ModuleFunctorHom F G}
-- given
  (h : η.natTrans = θ.natTrans) :
-- imply
  η = θ := by
-- proof
  apply CategoryTheory.ModuleFunctorHom.ext h


-- created on 2026-10-23
