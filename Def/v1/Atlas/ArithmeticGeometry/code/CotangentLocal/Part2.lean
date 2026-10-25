/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part2
open IsLocalRing


namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]

variable [IsScalarTower k R k]

noncomputable def derivRestrict (D : Derivation k R k) : (maximalIdeal R) →ₗ[k] k where
  toFun m := D m.val
  map_add' x y := by simp [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    show D (c • x).val = c * D x.val
    have : (c • x : maximalIdeal R).val = algebraMap k R c * x.val := by simp [Algebra.smul_def]
    rw [this, show algebraMap k R c * x.val = c • x.val from (Algebra.smul_def c x.val).symm]
    exact D.toLinearMap.map_smul c x.val

end CotangentDual
