/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
open IsLocalRing


namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]

variable [IsScalarTower k R k]

omit [IsLocalRing R] in
lemma algebraMap_comp_section (c : k) : algebraMap R k (algebraMap k R c) = c := by
  have := IsScalarTower.algebraMap_apply k R k c
  rw [Algebra.algebraMap_self_apply] at this; exact this.symm

omit [Algebra k R] [IsScalarTower k R k] in
lemma mem_maximalIdeal_map_zero
    (hφ : Function.Surjective (algebraMap R k)) (x : maximalIdeal R) :
    algebraMap R k x.val = 0 := by
  rw [← RingHom.mem_ker, IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) hφ]; exact x.2

end CotangentDual
