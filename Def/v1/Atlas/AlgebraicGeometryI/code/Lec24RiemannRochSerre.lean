/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement

@[expose] public section

set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

/-- The dimension `h⁰(ℙ¹, O(d)) = max(d + 1, 0)`. -/
def h0_P1 (d : ℤ) : ℕ := (d + 1).toNat

/-- The dimension `h¹(ℙ¹, O(d)) = max(-d - 1, 0)`, dual to `h⁰(ℙ¹, O(-d - 2))`. -/
def h1_P1 (d : ℤ) : ℕ := (-d - 1).toNat

end Lec24
end
