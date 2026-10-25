/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part7


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

def ClosedBall {n : ℕ} (center : Fin n → ℝ) (radius : ℝ)
    (x : Fin n → ℝ) : Prop :=
  l1Dist x center ≤ radius


def MapsClosedBall {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ)
    (center : Fin n → ℝ) (radius : ℝ) : Prop :=
  ∀ x, ClosedBall center radius x → ClosedBall center radius (F x)


end FiniteContraction
end Exact3D
end StatMech
