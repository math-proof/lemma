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
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part2

@[expose] public section

namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

noncomputable def iterate {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → Fin n → ℝ
  | 0, x => x
  | k + 1, x => F (iterate F k x)


end FiniteContraction
end Exact3D
end StatMech
