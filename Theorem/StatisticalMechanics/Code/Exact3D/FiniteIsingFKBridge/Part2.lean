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
import Def.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part2
open scoped BigOperators
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem freeFullVolumeQ2ThermodynamicLimitToIsing_of_finiteIsing
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
    FreeFullVolumeQ2ThermodynamicLimitToIsing β hβ := by
  filter_upwards [hIsing] with n hIsing_n
  exact Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun N =>
      finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
        hβ N n)
    hIsing_n


theorem freeInfiniteVolumeXAxisConnectionOfBetaQ2_le_freeTwoPoint_of_finiteIsing
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
    ∀ᶠ n in atTop,
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤
        |freeTwoPointOnXAxis β n| := by
  filter_upwards [hIsing] with n hIsing_n
  have hFK :=
    tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ n
  have hFull :
      Tendsto (fun N =>
        freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n)
        atTop (nhds |freeTwoPointOnXAxis β n|) := by
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N =>
        finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
          hβ N n)
      hIsing_n
  exact le_of_tendsto_of_tendsto hFK hFull
    (eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full β hβ n)


end Exact3D
end StatMech
