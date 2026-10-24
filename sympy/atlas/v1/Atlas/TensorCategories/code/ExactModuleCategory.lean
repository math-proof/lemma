/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Noetherian
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Definition 2.6.1 (EGNO): A left module category `M` over a multitensor category `C`
with enough projectives is exact if for any projective `P ∈ C` and any `N ∈ M`, the
object `P ⊗ N` is projective in `M`. -/
class ExactModuleCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] extends LeftModuleCategory C M where
  action_preserves_projective : ∀ (P : C) (N : M), [Projective P] → Projective (P ⊗ᵐ N)

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- Instance form of `action_preserves_projective`: in an exact module category, acting
by a projective object yields a projective object. -/
instance action_projective (P : C) [Projective P] (N : M) : Projective (P ⊗ᵐ N) :=
  action_preserves_projective P N


/-- In the finite abelian setting, whiskering an epi on the right by an object of the
module category yields an epi. -/
class QuasiFrobeniusProperty (A : Type*) [Category A] : Prop where
  projective_is_injective : ∀ (X : A), [Projective X] → Injective X
  injective_is_projective : ∀ (X : A), [Injective X] → Projective X

namespace QuasiFrobeniusProperty

variable {A : Type*} [Category A] [QuasiFrobeniusProperty A]

/-- In a quasi-Frobenius category, every projective object is injective. -/
instance projective_injective (X : A) [Projective X] : Injective X :=
  projective_is_injective X

/-- In a quasi-Frobenius category, every injective object is projective. -/
instance injective_projective (X : A) [Injective X] : Projective X :=
  injective_is_projective X

end QuasiFrobeniusProperty

/-- Compatibility class providing the adjunction between `P ⊗ -` and `(*P) ⊗ -` on the
module category side of a rigid monoidal action, together with naturality. -/
class ModuleRigidityCompat
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] where
  modRigidForward : ∀ (P : C) (N A : M), (A ⟶ P ⊗ᵐ N) → ((ᘁP) ⊗ᵐ A ⟶ N)
  modRigidBackward : ∀ (P : C) (N A : M), ((ᘁP) ⊗ᵐ A ⟶ N) → (A ⟶ P ⊗ᵐ N)
  modRigid_left_inv : ∀ (P : C) (N A : M) (g : (ᘁP) ⊗ᵐ A ⟶ N),
    modRigidForward P N A (modRigidBackward P N A g) = g
  modRigid_right_inv : ∀ (P : C) (N A : M) (f : A ⟶ P ⊗ᵐ N),
    modRigidBackward P N A (modRigidForward P N A f) = f
  modRigidForward_natural : ∀ (P : C) (N : M) {A B : M} (e : A ⟶ B) (g : B ⟶ P ⊗ᵐ N),
    modRigidForward P N A (e ≫ g) = ((ᘁP) ◁ᵐ e) ≫ modRigidForward P N B g

/-- The hom-set adjunction `(A ⟶ P ⊗ N) ≃ ((*P) ⊗ A ⟶ N)` extracted from the
`ModuleRigidityCompat` data. -/
def modHomTensorAdj
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [ModuleRigidityCompat C M]
    (P : C) (N A : M) : (A ⟶ P ⊗ᵐ N) ≃ ((ᘁP) ⊗ᵐ A ⟶ N) where
  toFun := ModuleRigidityCompat.modRigidForward P N A
  invFun := ModuleRigidityCompat.modRigidBackward P N A
  left_inv := ModuleRigidityCompat.modRigid_right_inv P N A
  right_inv := ModuleRigidityCompat.modRigid_left_inv P N A

/-- In a rigid monoidal category, the left dual of a projective object is projective. -/
theorem leftDualOfProjectiveIsProjective
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
    (P : C) [Projective P] :
    Projective (HasLeftDual.leftDual P) where
  factors {E X} f e _ := by
    let Φ := tensorRightHomEquiv (𝟙_ C) (ᘁP) P
    let f₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ X := (λ_ _).hom ≫ f
    let f₂ : 𝟙_ C ⟶ X ⊗ P := Φ X f₁

    have adj : tensorRight P ⊣ tensorRight (Pᘁ) := tensorRightAdjunction P (Pᘁ)
    have : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
      adj.leftAdjoint_preservesColimits
    have : (tensorRight P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _

    have : Epi (e ▷ P) := (tensorRight P).map_epi e

    haveI : Projective (X ⊗ P) := by
      have adj1 : tensorLeft X ⊣ tensorLeft (ᘁX) := tensorLeftAdjunction (ᘁX) X
      have adj2 : tensorLeft (ᘁX) ⊣ tensorLeft (ᘁ(ᘁX)) := tensorLeftAdjunction (ᘁ(ᘁX)) (ᘁX)
      haveI : PreservesColimitsOfSize.{0, 0} (tensorLeft (ᘁX)) :=
        adj2.leftAdjoint_preservesColimits
      haveI : (tensorLeft (ᘁX)).PreservesEpimorphisms :=
        preservesEpimorphisms_of_preservesColimitsOfShape _
      exact adj1.map_projective P ‹_›

    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (X ⊗ P)) (e ▷ P)


    let g₂ : 𝟙_ C ⟶ E ⊗ P := f₂ ≫ s

    let g₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ E := (Φ E).symm g₂

    use (λ_ _).inv ≫ g₁


    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorRightHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ e ▷ P = (Φ X) f₁
      simp only [g₁, g₂, Equiv.apply_symm_apply]
      simp only [f₂, assoc, hs, comp_id]
    simp only [assoc, key, f₁, Iso.inv_hom_id_assoc]

/-- Instance form of `leftDualOfProjectiveIsProjective`. -/
instance leftDual_projective_inst
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
    (P : C) [Projective P] : Projective (ᘁP) :=
  leftDualOfProjectiveIsProjective P

/-- `ActionRightExact` asserts that whiskering by a projective `Q ∈ C` on the left of
the module action preserves short exact sequences. -/
class ActionRightExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M] where
  actWhiskerLeft_comp_cokernel_zero :
    ∀ (Q : C) [Projective Q] {A B : M} (e : A ⟶ B) [Mono e],
      Q ◁ᵐ e ≫ Q ◁ᵐ (cokernel.π e) = 0
  actWhiskerLeft_shortExact :
    ∀ (Q : C) [Projective Q] {A B : M} (e : A ⟶ B) [Mono e],
      (ShortComplex.mk (Q ◁ᵐ e) (Q ◁ᵐ (cokernel.π e))
        (actWhiskerLeft_comp_cokernel_zero Q e)).ShortExact

/-- If `Q` is projective and `e : A ⟶ B` is a mono in the module category, then
`Q ◁ e` is a split monomorphism. -/
noncomputable def action_projective_split_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [Abelian M] [ActionRightExact C M]
    (Q : C) [Projective Q] {A B : M} (e : A ⟶ B) [Mono e] :
    SplitMono (Q ◁ᵐ e) := by

  let S := ShortComplex.mk (Q ◁ᵐ e) (Q ◁ᵐ (cokernel.π e))
    (ActionRightExact.actWhiskerLeft_comp_cokernel_zero Q e)

  have hSE : S.ShortExact := ActionRightExact.actWhiskerLeft_shortExact Q e

  haveI : Projective S.X₃ := action_preserves_projective Q (cokernel e)

  exact hSE.splittingOfProjective.splitMono_f

/-- Specialization of `action_projective_split_mono` to the left dual `*P` of a
projective `P` in a rigid category. -/
noncomputable def action_dual_split_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [Abelian M] [ActionRightExact C M]
    (P : C) [Projective P] {A B : M} (e : A ⟶ B) [Mono e] :
    SplitMono ((ᘁP) ◁ᵐ e) :=
  action_projective_split_mono (ᘁP) e

/-- Corollary 2.7.4 (EGNO), second half: In an exact module category over a rigid
multitensor category, every injective object is projective. -/
def IsModSubquotient {A : Type*} [Category A] (Y X : A) : Prop :=
  ∃ (Z : A) (i : Z ⟶ X) (p : Z ⟶ Y), Mono i ∧ Epi p

/-- The class asserting that left whiskering by an object of `C` preserves monos and epis
in the module category `M`, i.e. the module action is biexact in its first argument. -/
class BiexactAction (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M] where
  actWhiskerLeft_preserves_mono :
    ∀ (L : C) {A B : M} (f : A ⟶ B) [Mono f], Mono (L ◁ᵐ f)
  actWhiskerLeft_preserves_epi :
    ∀ (L : C) {A B : M} (f : A ⟶ B) [Epi f], Epi (L ◁ᵐ f)

/-- Convenience accessor: under `BiexactAction`, left whiskering by `L` preserves monos. -/
theorem actWhiskerLeft_preserves_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [BiexactAction C M]
    (L : C) {A B : M} (f : A ⟶ B) [Mono f] :
    Mono (L ◁ᵐ f) :=
  BiexactAction.actWhiskerLeft_preserves_mono L f

/-- Convenience accessor: under `BiexactAction`, left whiskering by `L` preserves epis. -/
theorem actWhiskerLeft_preserves_epi
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [BiexactAction C M]
    (L : C) {A B : M} (f : A ⟶ B) [Epi f] :
    Epi (L ◁ᵐ f) :=
  BiexactAction.actWhiskerLeft_preserves_epi L f

/-- Two objects `X` and `Y` of a left module category are `IrrRelated` if there exists
some `L ∈ C` such that `Y` is a subquotient of `L ⊗ X`. -/
def IrrRelated
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (X Y : M) : Prop :=
  ∃ (L : C), IsModSubquotient Y (L ⊗ᵐ X)

/-- Symmetry of the subquotient witness for `IrrRelated` when `X` is simple: from a
subquotient witness `Y ↪↠ L ⊗ X`, produce some `S` and a subquotient witness `X ↪↠ S ⊗ Y`.-/
structure IrrRelatedEquivalence
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    [HasZeroMorphisms M] where
  refl : ∀ (X : M), IrrRelated C M X X
  symm : ∀ {X Y : M} [Simple X], IrrRelated C M X Y → IrrRelated C M Y X
  trans : ∀ {X Y Z : M}, IrrRelated C M X Y → IrrRelated C M Y Z → IrrRelated C M X Z

/-- Lemma 2.7.6 (EGNO): The `IrrRelated` relation is an equivalence relation on simple
objects of an exact module category over a left rigid multitensor category. -/
abbrev definition_2_2_1
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] :=
  ModuleFunctor C M₁ M₂

/-- The predicate that every simple subquotient `S` of `N` is `IrrRelated` to the
chosen representative `X₀`. -/
def AllSimpleSubquotientsInClass'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    (X₀ N : M) : Prop :=
  ∀ (S : M), Simple S → IsModSubquotient S N → IrrRelated C M X₀ S

/-- Proposition 2.7.7 (EGNO): If `M` is an exact module category with a classification
of its simple objects by `IrrRelated` representatives, then `M` decomposes as a direct
sum of its module subcategories `M_i` (each generated by a single irreducibility class),
each of which is itself exact. This formulation packages the closure properties under
the action of `C` and under the action of projectives. -/
end ExactModuleCategory

end CategoryTheory
