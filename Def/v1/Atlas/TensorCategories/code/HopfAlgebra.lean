/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section HopfAlgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- Definition 1.22.2: the antipode of a Hopf algebra, as the `k`-linear map `S : H → H`
satisfying the equalities of Proposition 1.22.1. -/
def Definition_1_22_2_antipode (k : Type*) [CommSemiring k] (H : Type*) [Semiring H]
    [HopfAlgebra k H] : H →ₗ[k] H :=
  HopfAlgebra.antipode k

end HopfAlgebraRecap
