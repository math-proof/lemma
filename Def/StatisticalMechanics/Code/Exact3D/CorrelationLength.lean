/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.StatisticalMechanics.Code.Exact3D.CorrelationLength


namespace StatMech

namespace Exact3D

def TwoPointFunction {ι : Type*} (M : CriticalModel ι) : ℝ → ι → ι → ℝ :=
  M.twoPoint


def TwoPointAlongRay {ι : Type*} (M : CriticalModel ι) (β : ℝ) (origin : ι)
    (ray : ℕ → ι) (n : ℕ) : ℝ :=
  M.twoPoint β origin (ray n)


noncomputable def finiteDistanceDecayRate (G : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else -Real.log |G n| / (n : ℝ)


noncomputable def inverseDecayRate {ι : Type*} (M : CriticalModel ι) (β : ℝ)
    (origin : ι) (ray : ℕ → ι) (n : ℕ) : ℝ :=
  finiteDistanceDecayRate (TwoPointAlongRay M β origin ray) n


noncomputable def lowerInverseCorrelationLength {ι : Type*} (M : CriticalModel ι)
    (β : ℝ) (origin : ι) (ray : ℕ → ι) : ℝ :=
  Filter.liminf (inverseDecayRate M β origin ray) Filter.atTop


noncomputable def upperInverseCorrelationLength {ι : Type*} (M : CriticalModel ι)
    (β : ℝ) (origin : ι) (ray : ℕ → ι) : ℝ :=
  Filter.limsup (inverseDecayRate M β origin ray) Filter.atTop


def HasInverseCorrelationLength {ι : Type*} (M : CriticalModel ι) (β : ℝ)
    (origin : ι) (ray : ℕ → ι) (m : ℝ) : Prop :=
  Filter.Tendsto (inverseDecayRate M β origin ray) Filter.atTop (nhds m)


end Exact3D
end StatMech
