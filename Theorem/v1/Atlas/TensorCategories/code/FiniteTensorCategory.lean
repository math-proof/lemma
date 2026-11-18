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
public import Class.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part3
public section

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
public theorem endo_isIso_of_comp_epi_eq_of_localEnd
    {C : Type u} [Category.{v} C] [Abelian C]
    {P X : C} [Projective P] [Simple X]
    [IsLocalRing (End P)]
    (π : P ⟶ X) [Epi π] (f : End P) (hf : f.asHom ≫ π = π) : IsIso f.asHom := by
  set g : End P := 1 - f with hg_def

  have h1 : g.asHom ≫ π = 0 := by
    have key : g.asHom ≫ π = 𝟙 P ≫ π - f.asHom ≫ π := by
      show (1 - f).asHom ≫ π = 𝟙 P ≫ π - f.asHom ≫ π
      rw [End.sub_asHom, End.one_asHom]
      exact Preadditive.sub_comp (𝟙 P) f.asHom π
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
        _ = (inv g.asHom ≫ g.asHom) ≫ π := by rw [IsIso.inv_hom_id]
        _ = inv g.asHom ≫ (g.asHom ≫ π) := (Category.assoc _ _ _)
        _ = inv g.asHom ≫ 0 := by rw [h1]
        _ = 0 := Limits.comp_zero

    exact (indecomposable_of_simple X).1
      (by rw [Limits.IsZero.iff_id_eq_zero, ← cancel_epi π, hπ_zero, Limits.zero_comp, Limits.comp_zero])

end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
