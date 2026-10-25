/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.RegularObject
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
import Class.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part3
set_option maxHeartbeats 800000


universe w₀

open scoped TensorProduct


namespace CategoryTheory

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

/-- If `End P` is local, `P` is projective, and `X` is simple, then any endomorphism
`f` of `P` satisfying `f ≫ π = π` for an epi `π : P ⟶ X` is automatically an
isomorphism. -/
theorem endo_isIso_of_comp_epi_eq_of_localEnd
    {C : Type u} [Category.{v} C] [Abelian C]
    {P X : C} [Projective P] [Simple X]
    [IsLocalRing (End P)]
    (π : P ⟶ X) [Epi π] (f : End P) (hf : f ≫ π = π) : IsIso f := by
  set g : End P := 1 - f with hg_def

  have h1 : g ≫ π = 0 := by
    have key : g ≫ π = 𝟙 P ≫ π - f ≫ π := by
      show (1 - f) ≫ π = 𝟙 P ≫ π - f ≫ π
      rw [show (1 : End P) = (𝟙 P : End P) from rfl]
      exact Preadditive.sub_comp (𝟙 P) f π
    rw [key, Category.id_comp, hf, sub_self]

  have hlocal : IsUnit f ∨ IsUnit g := by
    apply IsLocalRing.isUnit_or_isUnit_of_add_one
    show f + (1 - f) = 1; simp
  cases hlocal with
  | inl hu =>

    rwa [isUnit_iff_isIso] at hu
  | inr hu =>

    rw [isUnit_iff_isIso] at hu
    exfalso
    have hπ_zero : π = 0 := by
      calc π = 𝟙 P ≫ π := (Category.id_comp π).symm
        _ = (inv g ≫ g) ≫ π := by rw [IsIso.inv_hom_id]
        _ = inv g ≫ (g ≫ π) := (Category.assoc _ _ _)
        _ = inv g ≫ 0 := by rw [h1]
        _ = 0 := comp_zero

    exact (indecomposable_of_simple X).1
      (by rw [IsZero.iff_id_eq_zero, ← cancel_epi π, hπ_zero, zero_comp, comp_zero])

end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
