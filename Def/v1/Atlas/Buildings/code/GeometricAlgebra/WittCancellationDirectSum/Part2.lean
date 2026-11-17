/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Order.RelClasses
public import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum

@[expose] public section

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
