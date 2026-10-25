/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part6
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

theorem dist_nonneg (x y : FinitePlusTailState n α) :
    0 ≤ x.dist y :=
  add_nonneg (FiniteContraction.l1Dist_nonneg x.finite y.finite)
    (SummableTail.dist_nonneg x.tail y.tail)


theorem finiteDist_nonneg (x y : FinitePlusTailState n α) :
    0 ≤ x.finiteDist y :=
  FiniteContraction.l1Dist_nonneg x.finite y.finite


theorem tailDist_nonneg (x y : FinitePlusTailState n α) :
    0 ≤ x.tailDist y :=
  SummableTail.dist_nonneg x.tail y.tail

@[simp] theorem ofFinite_finiteDist (x y : Fin n → ℝ) :
    (ofFinite (α := α) x).finiteDist (ofFinite y) =
      FiniteContraction.l1Dist x y :=
  rfl

@[simp] theorem ofFinite_tailDist (x y : Fin n → ℝ) :
    (ofFinite (α := α) x).tailDist (ofFinite y) = 0 := by
  simp [ofFinite, tailDist]

@[simp] theorem ofFinite_dist (x y : Fin n → ℝ) :
    (ofFinite (α := α) x).dist (ofFinite y) =
      FiniteContraction.l1Dist x y := by
  simp [dist, ofFinite]


theorem finiteDist_le_dist (x y : FinitePlusTailState n α) :
    x.finiteDist y ≤ x.dist y := by
  calc
    x.finiteDist y ≤ x.finiteDist y + x.tailDist y := by
      exact le_add_of_nonneg_right (tailDist_nonneg x y)
    _ = x.dist y := rfl


theorem tailDist_le_dist (x y : FinitePlusTailState n α) :
    x.tailDist y ≤ x.dist y := by
  calc
    x.tailDist y ≤ x.finiteDist y + x.tailDist y := by
      exact le_add_of_nonneg_left (finiteDist_nonneg x y)
    _ = x.dist y := rfl


@[simp] theorem dist_self (x : FinitePlusTailState n α) :
    x.dist x = 0 := by
  simp [dist, FiniteContraction.l1Dist_self]


theorem dist_comm (x y : FinitePlusTailState n α) :
    x.dist y = y.dist x := by
  simp [dist, FiniteContraction.l1Dist_comm, SummableTail.dist_comm]


theorem dist_triangle (x y z : FinitePlusTailState n α) :
    x.dist z ≤ x.dist y + y.dist z := by
  calc
    x.dist z =
        x.finiteDist z + x.tailDist z := rfl
    _ ≤
        (x.finiteDist y + y.finiteDist z) +
          (x.tailDist y + y.tailDist z) := by
      exact add_le_add
        (FiniteContraction.l1Dist_triangle x.finite y.finite z.finite)
        (SummableTail.dist_triangle x.tail y.tail z.tail)
    _ = x.dist y + y.dist z := by
      simp [dist, finiteDist, tailDist]
      ring


theorem eq_of_dist_eq_zero {x y : FinitePlusTailState n α}
    (h : x.dist y = 0) : x = y := by
  apply ext
  · apply FiniteContraction.l1Dist_eq_zero_iff.mp
    exact le_antisymm
      (by simpa [h, finiteDist] using finiteDist_le_dist x y)
      (FiniteContraction.l1Dist_nonneg x.finite y.finite)
  · apply SummableTail.eq_of_dist_eq_zero
    exact le_antisymm
      (by simpa [h, tailDist] using tailDist_le_dist x y)
      (SummableTail.dist_nonneg x.tail y.tail)


end FinitePlusTailState
end Exact3D
end StatMech
