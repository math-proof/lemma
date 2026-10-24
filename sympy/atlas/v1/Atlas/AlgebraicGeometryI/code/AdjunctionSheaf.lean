/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

noncomputable section

open scoped TensorProduct
open KaehlerDifferential Module

universe u v


section ConormalExactSequenceQuotient

variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (I : Ideal R)
