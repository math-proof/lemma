module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
public import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part4
public section
set_option maxHeartbeats 800000

universe w₀

open scoped TensorProduct

namespace CategoryTheory

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

/-- A category in which every projective object is injective (the quasi-Frobenius
property at the level of `C`). -/
class HasProjectiveImpliesInjective (C : Type u) [Category.{v} C] : Prop where
  injective_of_projective : ∀ (P : C) [Projective P], Injective P

/-- A rigid abelian monoidal category with enough projectives is asserted to also have
enough injectives. -/
class HasEnoughInjectivesFromRigid (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [EnoughProjectives C] : Prop where
  enoughInj : EnoughInjectives C

/-- Axiomatic Jordan-Hölder multiplicity of a simple object `X` in `Y`. -/
class HasJordanHolderMultiplicity (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] where
  multiplicity : (X : C) → [Simple X] → (Y : C) → ℕ
  multiplicity_self : ∀ (X : C) [Simple X], multiplicity X X = 1

/-- The formula relating Hom-space dimension to Jordan-Hölder multiplicity:
`dim_k Hom(P_X, Y) = [Y : X]` for the projective cover `P_X` of a simple `X`. -/
class HasHomMultiplicityFormula (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [EnoughProjectives C]
    [HasJordanHolderMultiplicity k C] where
  dim_hom_projCover_eq :
    ∀ (X : C) [Simple X] (Y : C),
      Module.finrank k (Projective.over X ⟶ Y) =
        HasJordanHolderMultiplicity.multiplicity (k := k) X Y

end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
