/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.ThetaZeroBelowPc
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge
open scoped BigOperators
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


def FreeIsingXAxisThermodynamicLimitToFiniteVolumes (β : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    Tendsto (fun N => finiteIsingXAxisTwoPointInVolume β N n)
      atTop (nhds |freeTwoPointOnXAxis β n|)


def FreeFullVolumeQ2ThermodynamicLimitToIsing
    (β : ℝ) (hβ : 0 < β) : Prop :=
  ∀ᶠ n in atTop,
    Tendsto (fun N =>
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n)
      atTop (nhds |freeTwoPointOnXAxis β n|)


end Exact3D
end StatMech
