/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Int.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre
set_option maxHeartbeats 800000


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
