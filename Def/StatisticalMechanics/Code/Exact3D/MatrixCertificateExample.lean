/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

noncomputable def stableMatrix : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : ℝ) / 2
  | ⟨1, _⟩, ⟨1, _⟩ => (1 : ℝ) / 3
  | _, _ => 0


def stableIntervals : RatInterval.IntervalMatrix 2 2
  | ⟨0, _⟩, ⟨0, _⟩ => RatInterval.point (1 / 2)
  | ⟨1, _⟩, ⟨1, _⟩ => RatInterval.point (1 / 3)
  | _, _ => RatInterval.point 0


def stableMatrixQ : Fin 2 → Fin 2 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩, ⟨1, _⟩ => 1 / 3
  | _, _ => 0


end MatrixCertificateExample
end Exact3D
end StatMech
