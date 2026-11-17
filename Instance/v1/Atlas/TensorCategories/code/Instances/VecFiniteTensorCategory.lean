/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Instances/VecFiniteTensorCategory.lean -/

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
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Projective
public import Class.v1.Atlas.TensorCategories.code.Instances.VecFiniteTensorCategory

@[expose] public section

set_option maxHeartbeats 400000

open CategoryTheory

universe u


namespace CategoryTheory

namespace FGModuleCat

variable (K : Type u) [Field K]

/-- Every finite-dimensional vector space (viewed as an object of `FGModuleCat K`) is projective. -/
noncomputable instance instProjective (V : FGModuleCat.{u} K) :
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

/-- `FGModuleCat K` has enough projectives, witnessed trivially by `V ↠ V` (since every object
is projective). -/
noncomputable instance instEnoughProjectives :
    EnoughProjectives (FGModuleCat.{u} K) where
  presentation V := ⟨{
    p := V
    f := 𝟙 V
  }⟩

/-- `FGModuleCat K`, the category of finite-dimensional `K`-vector spaces, is a finite tensor
category over `K`. -/
noncomputable instance instFiniteTensorCategory :
    FiniteTensorCategory' K (FGModuleCat.{u} K) where
  enoughProj := inferInstance
  homFiniteDim _ _ := inferInstance

end FGModuleCat
end CategoryTheory
