/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.CotangentLocal
open IsLocalRing


namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]

variable [IsScalarTower k R k]

noncomputable def projMaxIdeal
    (hφ : Function.Surjective (algebraMap R k)) (r : R) : maximalIdeal R :=
  ⟨r - algebraMap k R (algebraMap R k r), by
    rw [← IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) hφ, RingHom.mem_ker, map_sub,
      ← IsScalarTower.algebraMap_apply k R k]; simp⟩

end CotangentDual
