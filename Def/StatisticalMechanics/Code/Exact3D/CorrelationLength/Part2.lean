/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Structure.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part2

@[expose] public section

namespace StatMech

namespace Exact3D

noncomputable def liminfCorrelationLength {ι : Type*} (M : CriticalModel ι)
    (β : ℝ) (origin : ι) (ray : ℕ → ι) : ℝ :=
  (lowerInverseCorrelationLength M β origin ray)⁻¹


noncomputable def logSlope {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (β : ℝ) : ℝ :=
  -Real.log (correlationLength β) / Real.log (M.betaC - β)


def HasCriticalNu {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (ν : ℝ) : Prop :=
  Filter.Tendsto (logSlope M correlationLength)
    (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ν)

end Exact3D
end StatMech
