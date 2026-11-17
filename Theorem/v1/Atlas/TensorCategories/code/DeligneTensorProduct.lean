/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Structure.v1.Atlas.TensorCategories.code.DeligneTensorProductDef
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Def.v1.Atlas.TensorCategories.code.DeligneTensorProduct
set_option maxHeartbeats 400000

public section

noncomputable section

open TensorProduct CategoryTheory ModuleCat

namespace Deligne

variable (k : Type) [CommRing k]

section ModuleAction

variable (A : Type) [Ring A] [Algebra k A]

variable (B : Type) [Ring B] [Algebra k B]

variable (M : Type) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]

variable (N : Type) [AddCommGroup N] [Module k N] [Module B N]
  [IsScalarTower k B N] [SMulCommClass k B N]

/-- The actions of `A` (on the left factor) and `B` (on the right factor) on `M ⊗ N`
commute as endomorphisms of `M ⊗[k] N`. -/
theorem actA_actB_commute (a : A) (b : B) :
    Commute (actA k A M N a) (actB k B M N b) := by
  unfold actA actB
  simp only [AlgHom.comp_apply]
  rw [Commute, SemiconjBy]
  change (((Algebra.lsmul k k M) a).rTensor N).comp
      (((Algebra.lsmul k k N) b).lTensor M) =
    (((Algebra.lsmul k k N) b).lTensor M).comp
      (((Algebra.lsmul k k M) a).rTensor N)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

end ModuleAction
end Deligne
end
