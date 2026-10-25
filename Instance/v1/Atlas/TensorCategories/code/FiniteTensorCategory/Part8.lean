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
import Def.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part7
set_option maxHeartbeats 800000


universe w₀

open scoped TensorProduct


namespace CategoryTheory

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

attribute [instance] FiniteTensorCategoryData.ι_fintype
  FiniteTensorCategoryData.ι_decidableEq FiniteTensorCategoryData.ι_nonempty

section FPdimInequalityLemmas

variable {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [EnoughProjectives C]
    [HasCategoricalFPdim C] [h : HasFPdimInequality C]

section FGModuleCatInstance

universe u_fgm

variable (K : Type u_fgm) [Field K]

/-- Every finite-dimensional `K`-module is a projective object in `FGModuleCat K`, by
transferring projectivity from `ModuleCat K` along the forgetful functor. -/
noncomputable instance fgModuleCat_projective (V : FGModuleCat.{u_fgm} K) :
    Projective V := by
  constructor
  intro E X f e he
  set F := forget₂ (FGModuleCat K) (ModuleCat K)
  haveI : Projective (F.obj V) := inferInstance
  haveI : Epi (F.map e) := Functor.map_epi F e
  obtain ⟨g, hg⟩ := Projective.factors (F.map f) (F.map e)
  haveI : F.Full := inferInstance
  obtain ⟨g', rfl⟩ := F.map_surjective g
  refine ⟨g', ?_⟩
  haveI : F.Faithful := inferInstance
  exact F.map_injective (by rw [F.map_comp, hg])

/-- The category `FGModuleCat K` has enough projectives: every object is itself projective,
so it serves as its own projective presentation via the identity morphism. -/
noncomputable instance fgModuleCat_enoughProjectives :
    EnoughProjectives (FGModuleCat.{u_fgm} K) where
  presentation V := ⟨{
    p := V
    f := 𝟙 V
  }⟩

/-- The category `FGModuleCat K` of finite-dimensional `K`-vector spaces is the prototypical
example of a finite tensor category over `K`. -/
noncomputable instance instFiniteTensorCategoryFGModuleCat :
    FiniteTensorCategory K (FGModuleCat.{u_fgm} K) where
  enoughProj := inferInstance
  homFiniteDim _ _ := inferInstance

end FGModuleCatInstance
end FPdimInequalityLemmas
end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
