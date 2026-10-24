import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
open CategoryTheory CategoryTheory.ExactModuleCategory
open Category MonoidalCategory LeftModCat Limits


namespace CategoryTheory.ExactModuleCategory

/--
[enoughProjectives_of_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma enoughProjectives_of_exact
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [EnoughProjectives C]
-- given
  (hEpi : ∀ {X Y : C} (f : X ⟶ Y) (N : M), Epi f → Epi (f ▷ᵐ N)) :
-- imply
  EnoughProjectives M where presentation N := by
-- proof
  obtain ⟨pp⟩ := EnoughProjectives.presentation (𝟙_ C)
  exact ⟨{
    p := pp.p ⊗ᵐ N
    projective := @action_preserves_projective _ _ _ _ _ _ pp.p N pp.projective
    f := pp.f ▷ᵐ N ≫ (actℓ_ N).hom
    epi := by
      have : Epi (pp.f ▷ᵐ N) := hEpi pp.f N pp.epi
      exact epi_comp (pp.f ▷ᵐ N) (actℓ_ N).hom
  }⟩

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[modHomTensorAdj_natural](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma modHomTensorAdj_natural
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [LeftRigidCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [ModuleRigidityCompat C M]
  {P : C}
  {N : M}
  {A B : M}
  {e : A ⟶ B}
  {g : B ⟶ P ⊗ᵐ N} :
-- imply
  modHomTensorAdj P N A (e ≫ g) = ((ᘁP) ◁ᵐ e) ≫ modHomTensorAdj P N B g :=
-- proof
  ModuleRigidityCompat.modRigidForward_natural P N e g

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[action_injective_of_rigid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma action_injective_of_rigid
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [ModuleRigidityCompat C M]
  [Abelian M]
  [ActionRightExact C M]
  {P : C}
  [Projective P]
  {N : M} :
-- imply
  Injective (P ⊗ᵐ N) where factors {A B} f e _ := by
-- proof
  let sm := action_dual_split_mono (C := C) (M := M) P e
  let r := sm.retraction
  have hr := sm.id
  let adj := modHomTensorAdj (C := C) (M := M) P N
  refine ⟨(adj B).symm (r ≫ adj A f), ?_⟩
  apply (adj A).injective
  show modHomTensorAdj P N A
    (e ≫ (modHomTensorAdj P N B).symm (r ≫
      modHomTensorAdj P N A f)) =
    modHomTensorAdj P N A f
  rw [modHomTensorAdj_natural P N e]
  rw [Equiv.apply_symm_apply]
  rw [← assoc, hr, id_comp]

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[injective_of_retract](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma injective_of_retract
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Category A]
  {I X : A}
  [Injective I]
  {s : X ⟶ I}
  {r : I ⟶ X}
-- given
  (hr : s ≫ r = 𝟙 X) :
-- imply
  Injective X where factors {B D} g f _ := by
-- proof
  obtain ⟨h, hh⟩ := Injective.factors (g ≫ s) f
  exact ⟨h ≫ r, by rw [← assoc, hh, assoc, hr, comp_id]⟩

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[projective_is_injective_of_exact_rigid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma projective_is_injective_of_exact_rigid
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [EnoughProjectives C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [ModuleRigidityCompat C M]
  [Abelian M]
  [ActionRightExact C M]
  {X : M}
  [Projective X]
-- given
  (hEpi : ∀ {X Y : C} (f : X ⟶ Y) (N : M), Epi f → Epi (f ▷ᵐ N)) :
-- imply
  Injective X := by
-- proof
  obtain ⟨pp⟩ := EnoughProjectives.presentation (𝟙_ C)
  have hEpi_f : Epi (pp.f ▷ᵐ X) := hEpi pp.f X pp.epi
  let e : pp.p ⊗ᵐ X ⟶ X := pp.f ▷ᵐ X ≫ (actℓ_ X).hom
  have he : Epi e := epi_comp (pp.f ▷ᵐ X) (actℓ_ X).hom
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 X) e
  haveI : Projective pp.p := pp.projective
  haveI : Injective (pp.p ⊗ᵐ X) := action_injective_of_rigid pp.p X
  exact injective_of_retract s e hs

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[isModSubquotient_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma isModSubquotient_trans
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Category A]
  [Abelian A]
  {X Y Z : A} :
-- imply
  IsModSubquotient Y X → IsModSubquotient Z Y → IsModSubquotient Z X := by
-- proof
  intro ⟨W₁, i₁, p₁, hi₁, hp₁⟩ ⟨W₂, i₂, p₂, hi₂, hp₂⟩
  haveI := hi₁; haveI := hp₁; haveI := hi₂; haveI := hp₂
  refine ⟨pullback p₁ i₂, pullback.fst p₁ i₂ ≫ i₁, pullback.snd p₁ i₂ ≫ p₂, ?_, ?_⟩
  · haveI : Mono (pullback.fst p₁ i₂) := pullback.fst_of_mono
    exact mono_comp _ _
  · exact epi_comp _ _

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[irrRelated_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma irrRelated_refl
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory C M]
  {X : M} :
-- imply
  IrrRelated C M X X :=
-- proof
  ⟨𝟙_ C, X, (actℓ_ X).inv, 𝟙 X,
    inferInstance, inferInstance⟩

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[irrRelated_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma irrRelated_trans
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [BiexactAction C M]
  {X Y Z : M} :
-- imply
  IrrRelated C M X Y → IrrRelated C M Y Z → IrrRelated C M X Z := by
-- proof
  intro ⟨L₁, hXY⟩ ⟨L₂, hYZ⟩
  refine ⟨L₂ ⊗ L₁, ?_⟩
  have hL₂Y : IsModSubquotient (L₂ ⊗ᵐ Y) (L₂ ⊗ᵐ (L₁ ⊗ᵐ X)) := by
    obtain ⟨W, i, p, hi, hp⟩ := hXY
    exact ⟨L₂ ⊗ᵐ W, L₂ ◁ᵐ i, L₂ ◁ᵐ p,
      @actWhiskerLeft_preserves_mono C _ _ M _ _ _ _ L₂ _ _ i hi,
      @actWhiskerLeft_preserves_epi C _ _ M _ _ _ _ L₂ _ _ p hp⟩
  have hZ_L₂L₁X : IsModSubquotient Z (L₂ ⊗ᵐ (L₁ ⊗ᵐ X)) :=
    isModSubquotient_trans hL₂Y hYZ
  obtain ⟨W, i, p, hi, hp⟩ := hZ_L₂L₁X
  exact ⟨W, i ≫ (actμ_ L₂ L₁ X).inv, p,
    mono_comp i (actμ_ L₂ L₁ X).inv, hp⟩

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[nonzero_hom_yields_subquotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma nonzero_hom_yields_subquotient
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Category A]
  [Abelian A]
  {X T : A}
  [Simple X]
  {f : X ⟶ T}
-- given
  (hf : f ≠ 0) :
-- imply
  IsModSubquotient X T := by
-- proof
  haveI : Mono f := mono_of_nonzero_from_simple hf
  exact ⟨X, f, 𝟙 X, inferInstance, inferInstance⟩

end CategoryTheory.ExactModuleCategory

namespace CategoryTheory.ExactModuleCategory

/--
[lemma_2_7_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
lemma lemma_2_7_3
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [ModuleRigidityCompat C M]
  [ActionRightExact C M]
  {P : C}
  [Projective P]
  {N : M} :
-- imply
  Injective (P ⊗ᵐ N) :=
-- proof
  action_injective_of_rigid P N

end CategoryTheory.ExactModuleCategory

/--
[leftDualOfProjectiveIsProjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
private lemma leftDualOfProjectiveIsProjective_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {P : C}
  [Projective P] :
-- imply
  Projective (HasLeftDual.leftDual P) where factors {E X} f e _ := by
-- proof
  apply CategoryTheory.ExactModuleCategory.leftDualOfProjectiveIsProjective P

/--
[actWhiskerLeft_preserves_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
private lemma actWhiskerLeft_preserves_mono_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [BiexactAction C M]
  {L : C}
  {A B : M}
  {f : A ⟶ B}
  [Mono f] :
-- imply
  Mono (L ◁ᵐ f) := by
-- proof
  apply CategoryTheory.ExactModuleCategory.actWhiskerLeft_preserves_mono L f

/--
[actWhiskerLeft_preserves_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean)
-/
@[path]
private lemma actWhiskerLeft_preserves_epi_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [BiexactAction C M]
  {L : C}
  {A B : M}
  {f : A ⟶ B}
  [Epi f] :
-- imply
  Epi (L ◁ᵐ f) := by
-- proof
  apply CategoryTheory.ExactModuleCategory.actWhiskerLeft_preserves_epi L f


-- created on 2026-10-23
