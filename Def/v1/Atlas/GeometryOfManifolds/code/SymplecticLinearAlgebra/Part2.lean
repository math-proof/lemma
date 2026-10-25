/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
open Module


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The linear map $V \to E^*$ sending $v \mapsto \Omega(\cdot, v)|_E$, used to identify $V/E$ with
the dual of a Lagrangian. -/
noncomputable def symplRestrict (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) :
    V →ₗ[ℝ] (↥E →ₗ[ℝ] ℝ) where
  toFun v := (Ω.flip v).domRestrict E
  map_add' x y := by ext e; simp [LinearMap.domRestrict, map_add, LinearMap.add_apply]
  map_smul' r x := by ext e; simp [LinearMap.domRestrict, map_smul, LinearMap.smul_apply]

end SymplecticLinearAlgebra
