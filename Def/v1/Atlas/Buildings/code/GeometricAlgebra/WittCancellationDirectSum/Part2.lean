/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.RelClasses
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum
set_option maxHeartbeats 2000000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]


/-- A bilinear form is nondegenerate (in the orthogonal-complement sense) if
the orthogonal complement of the whole space is trivial. -/
def IsNondegenerate'
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥

/-- A bilinear form is symmetric: `B x y = B y x` for all `x, y`. -/
def IsSymmetric'
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  ∀ x y : V, B x y = B y x


end Garrett
