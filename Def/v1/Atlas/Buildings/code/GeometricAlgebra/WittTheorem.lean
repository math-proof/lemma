/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Fin.Nondegenerate.of.EqOrthogonalBilinFormTop_Bot.IsRefl
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop
set_option maxHeartbeats 4000000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]

variable {V : Type*} [AddCommGroup V] [Module k V]


variable (B : LinearMap.BilinForm k V)

/-- Bilinear reflection of `v` through the hyperplane orthogonal to a non-isotropic
vector `a`: subtracts off twice the `a`-component measured by `B`. -/
noncomputable def bilinReflect (a : V) (_ha : B a a ≠ 0) (v : V) : V :=
  v - (2 * B v a / B a a) • a

/-- The bilinear reflection through `a` packaged as a linear map `V →ₗ[k] V`. -/
noncomputable def bilinReflectLM (a : V) (ha : B a a ≠ 0) : V →ₗ[k] V where
  toFun := bilinReflect B a ha
  map_add' := by
    intro x y
    simp only [bilinReflect, map_add, LinearMap.add_apply]
    module
  map_smul' := by
    intro c x
    simp only [bilinReflect, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    module

end Garrett
