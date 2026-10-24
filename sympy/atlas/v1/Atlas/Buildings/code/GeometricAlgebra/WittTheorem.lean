/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
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

/-- The bilinear reflection is an involution: applying it twice returns the
original vector. -/
theorem bilinReflect_invol (a : V) (ha : B a a ≠ 0) (v : V) :
    bilinReflect B a ha (bilinReflect B a ha v) = v := by
  simp only [bilinReflect]
  set c := 2 * B v a / B a a with hc_def

  have hBva : B (v - c • a) a = B v a - c * B a a := by
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hBva]

  have hcoeff : 2 * (B v a - c * B a a) / B a a = -c := by
    rw [hc_def]; field_simp; ring
  rw [hcoeff]

  simp [neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The bilinear reflection through `a`, packaged as a linear equivalence
`V ≃ₗ[k] V` (using its involutive property). -/
noncomputable def bilinReflectEquiv (a : V) (ha : B a a ≠ 0) : V ≃ₗ[k] V :=
  LinearEquiv.ofInvolutive (bilinReflectLM B a ha) (bilinReflect_invol B a ha)
