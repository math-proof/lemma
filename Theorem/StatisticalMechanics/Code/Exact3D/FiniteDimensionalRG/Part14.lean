/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15


namespace StatMech

namespace Exact3D

namespace TwoCoordinateRGData

theorem iterate_eq (D : TwoCoordinateRGData) (n : ℕ) (x : ℝ × ℝ) :
    D.iterate n x = (D.thermal ^ n * x.1, D.stable ^ n * x.2) := by
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      simp [iterate, ih, rgMap, pow_succ', mul_assoc]


theorem stable_iterate_abs_eq (D : TwoCoordinateRGData) (n : ℕ) (s : ℝ) :
    |(D.iterate n (0, s)).2| = |D.stable| ^ n * |s| := by
  simp [iterate_eq, abs_mul, abs_pow]


theorem stable_multiplier_lt_one (D : TwoCoordinateRGData) :
    |D.stable| < 1 :=
  D.stable_abs_lt_one


end TwoCoordinateRGData
end Exact3D
end StatMech
