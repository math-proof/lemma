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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part7


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

theorem step_origin {n : ℕ} (H : FiniteHyperbolicSplitting n) :
    H.step origin = origin := by
  apply Prod.ext
  · simp [origin, step]
  · simpa [origin, step] using H.stable.step_zero


theorem iterate_origin {n : ℕ} (H : FiniteHyperbolicSplitting n) (k : ℕ) :
    H.iterate k origin = origin := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, H.step_origin]


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
