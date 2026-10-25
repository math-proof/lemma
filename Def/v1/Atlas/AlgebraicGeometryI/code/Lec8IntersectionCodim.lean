/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8IntersectionCodim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem


noncomputable section

open Ideal

/-- Krull dimension of a commutative ring as a natural number
(returning `0` in degenerate or infinite cases). -/
def dimNat (R : Type*) [CommRing R] : ℕ :=
  (Option.getD (ringKrullDim R) ⊤).toNat

end
