/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Projective
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
public import Theorem.Category.Atlas.v1.TensorCategories.code.RegularObject
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
public import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
public import Class.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part6

@[expose] public section

set_option maxHeartbeats 800000


universe w₀

open scoped TensorProduct


namespace CategoryTheory
open Limits
open MonoidalCategory

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

/-- In a rigid monoidal category with projective unit, both duals of any projective
object are again projective. -/
noncomputable instance (priority := 100) hasDualProjectiveProperty_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [HasZeroMorphisms C] [Projective (𝟙_ C)] :
    HasDualProjectiveProperty C where
  rightDual_projective P := Projective.mk (fun {E X} f e => by
    intro
    let Φ := tensorLeftHomEquiv (𝟙_ C) P (HasRightDual.rightDual P)
    let f₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ X := (ρ_ _).hom ≫ f
    let f₂ : 𝟙_ C ⟶ P ⊗ X := Φ X f₁
    have adj : tensorLeft P ⊣ tensorLeft (ᘁP) := tensorLeftAdjunction (ᘁP) P
    haveI : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
      adj.leftAdjoint_preservesColimits
    haveI : (tensorLeft P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    have : Epi (P ◁ e) := (tensorLeft P).map_epi e
    obtain ⟨g₂, hg₂⟩ := Projective.factors f₂ (P ◁ e)
    let g₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ E := (Φ E).symm g₂
    refine ⟨(ρ_ _).inv ≫ g₁, ?_⟩
    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorLeftHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ P ◁ e = (Φ X) f₁
      simp only [g₁, Equiv.apply_symm_apply]
      exact hg₂
    simp only [Category.assoc, key, f₁, Iso.inv_hom_id_assoc])
  leftDual_projective P := Projective.mk (fun {E X} f e => by
    intro
    let Φ := tensorRightHomEquiv (𝟙_ C) (ᘁP) P
    let f₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ X := (λ_ _).hom ≫ f
    let f₂ : 𝟙_ C ⟶ X ⊗ P := Φ X f₁
    have adj : tensorRight P ⊣ tensorRight (Pᘁ) := tensorRightAdjunction P (Pᘁ)
    haveI : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
      adj.leftAdjoint_preservesColimits
    haveI : (tensorRight P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    have : Epi (e ▷ P) := (tensorRight P).map_epi e
    obtain ⟨g₂, hg₂⟩ := Projective.factors f₂ (e ▷ P)
    let g₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ E := (Φ E).symm g₂
    refine ⟨(λ_ _).inv ≫ g₁, ?_⟩
    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorRightHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ e ▷ P = (Φ X) f₁
      simp only [g₁, Equiv.apply_symm_apply]
      exact hg₂
    simp only [Category.assoc, key, f₁, Iso.inv_hom_id_assoc])

end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
