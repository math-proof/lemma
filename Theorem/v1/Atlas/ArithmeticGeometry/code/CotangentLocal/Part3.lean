/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part2
open IsLocalRing


namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]

variable [IsScalarTower k R k]

omit [IsScalarTower k R k] in
lemma derivRestrict_vanishes
    (hφ : Function.Surjective (algebraMap R k))
    (D : Derivation k R k) (x y : maximalIdeal R) :
    derivRestrict D (x * y) = 0 := by
  show D (x.val * y.val) = 0
  rw [D.leibniz]
  simp [Algebra.smul_def, mem_maximalIdeal_map_zero hφ x, mem_maximalIdeal_map_zero hφ y]

end CotangentDual
