/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Pi
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton

@[expose] public section

namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

def LipschitzWithConstant {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x y, l1Dist (F x) (F y) ≤ c * l1Dist x y


end FiniteContraction
end Exact3D
end StatMech
