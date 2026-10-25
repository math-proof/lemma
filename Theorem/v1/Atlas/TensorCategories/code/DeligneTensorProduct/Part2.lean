/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.DeligneTensorProductDef
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Def.v1.Atlas.TensorCategories.code.DeligneTensorProduct.Part2
set_option maxHeartbeats 400000


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

/-- Computation rule for the `(A ⊗ B)`-action on `M ⊗ N`: the pure tensor
`(a ⊗ b) • (m ⊗ n)` equals `(a • m) ⊗ (b • n)`. -/
theorem actAB_tmul_tmul (a : A) (b : B) (m : M) (n : N) :
    actAB k A B M N (a ⊗ₜ[k] b) (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) := by
  unfold actAB
  simp [Algebra.TensorProduct.lift_tmul]
  unfold actA actB
  simp [AlgHom.comp_apply, Module.End.rTensorAlgHom_apply_apply,
        Module.End.lTensorAlgHom_apply_apply]
  simp [liftAux_tmul, Algebra.lsmul_coe, LinearMap.compl₂_apply, mk_apply]

end ModuleAction
end Deligne
end
