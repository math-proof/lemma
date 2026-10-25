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
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part2
set_option maxHeartbeats 800000


universe w₀

open scoped TensorProduct


namespace CategoryTheory

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

/-- Existence of a projective cover for any simple object, given enough projectives and
the projective cover minimality property. -/
noncomputable def exists_projective_cover_of_simple
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    [HasProjectiveCoversOfSimples C]
    (X : C) [Simple X] : Σ P, IsProjectiveCover P X :=
  haveI : Projective (Projective.over X) := Projective.projective_over X
  haveI : Epi (Projective.π X) := Projective.π_epi X
  ⟨Projective.over X,
    { π := Projective.π X
      proj := inferInstance
      epi_π := inferInstance
      minimal := fun f hf =>
        HasProjectiveCoversOfSimples.endo_isIso_of_comp_epi_eq _ X _ f hf }⟩

end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
