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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre
set_option maxHeartbeats 800000

public section

noncomputable section

namespace Lec24

/-- Euler characteristic of `O(d)` on `ℙ¹`: `χ(O(d)) = h⁰ - h¹ = d + 1`. -/
theorem euler_char_O_d_P1 (d : ℤ) : (h0_P1 d : ℤ) - (h1_P1 d : ℤ) = d + 1 := by
  unfold h0_P1 h1_P1
  by_cases h : 0 ≤ d + 1
  · rw [Int.toNat_of_nonneg h]
    by_cases h2 : 0 ≤ -d - 1
    · rw [Int.toNat_of_nonneg h2]; omega
    · rw [Int.toNat_eq_zero.mpr (by omega : -d - 1 ≤ 0)]; omega
  · rw [Int.toNat_eq_zero.mpr (by omega : d + 1 ≤ 0)]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -d - 1)]; omega

end Lec24
end
