/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
import Theorem.v1.Atlas.LieGroups.code.DModules
universe u v w


namespace DModules

open scoped TensorProduct

section Prop289

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]

variable {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

noncomputable def LeftDModule.ofFlatConnection (conn : Connection k A M)
    (hflat : conn.IsFlat) : LeftDModule k A M where
  vecFieldAction v := covariantDerivative v conn
  vecFieldAction_smul v f m := by
    simp only [covariantDerivative, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [conn.leibniz f m]
    simp [map_add, map_smul, TensorProduct.mk_apply, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, Derivation.liftKaehlerDifferential_comp_D]
  vecFieldAction_smul_vec f v m := by
    simp only [covariantDerivative, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [liftKaehlerDifferential_smul, LinearMap.lTensor_smul, LinearMap.smul_apply,
      LinearMap.map_smul]
  vecFieldAction_lie v w m := by
    have h := hflat v w
    have key := LinearMap.ext_iff.mp h m
    simp only [curvature, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] at key
    exact sub_eq_zero.mp key

end Prop289
end DModules
