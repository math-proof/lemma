/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HilbertNoether.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.FiniteType

section HilbertNoether

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]

instance fixedPoints_isInvariant :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩
