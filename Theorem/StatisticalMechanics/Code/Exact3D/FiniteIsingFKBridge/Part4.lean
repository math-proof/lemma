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
import Def.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
open scoped BigOperators
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem freeXAxisQ2ConnectionAgrees_of_finiteVolume_restrictedCylinderComparison
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hrestricted : FreeFiniteIsingFKXAxisRestrictedCylinderComparison β hβ) :
    FreeXAxisQ2ConnectionAgrees β hβ := by
  unfold FreeXAxisQ2ConnectionAgrees FreeXAxisFKConnectionAgrees
  filter_upwards [hIsing, hrestricted] with n hIsing_n hrestricted_n
  have hFK :=
    tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ n
  have hIsing_to_fk :
      Tendsto (fun N => finiteIsingXAxisTwoPointInVolume β N n)
        atTop (nhds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)) := by
    exact Filter.Tendsto.congr' (hrestricted_n.mono fun _ h => h.symm) hFK
  exact tendsto_nhds_unique hIsing_n hIsing_to_fk


theorem fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing
    {β A m : ℝ} (hβ : 0 < β) :
    FKXAxisConnectionExactExponentialDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (finiteIsingXAxisTwoPointBox β) A m :=
  FKXAxisConnectionExactExponentialDecay.congr_eventually_iff <| by
    filter_upwards with n
    exact finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n


theorem fkXAxisConnectionExactExponentialDecay_finiteIsing_iff_freeFiniteVolumeQ2
    {β A m : ℝ} (hβ : 0 < β) :
    FKXAxisConnectionExactExponentialDecay
      (finiteIsingXAxisTwoPointBox β) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m :=
  (fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing
    hβ).symm


theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (finiteIsingXAxisTwoPointBox β) A m :=
  FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff <| by
    filter_upwards with n
    exact finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n


theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_finiteIsing_iff_freeFiniteVolumeQ2
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (finiteIsingXAxisTwoPointBox β) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m :=
  (fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing
    hβ).symm


theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (finiteIsingXAxisTwoPointBox β) Alo Ahi m :=
  FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff <| by
    filter_upwards with n
    exact finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n


theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_finiteIsing_iff_freeFiniteVolumeQ2
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (finiteIsingXAxisTwoPointBox β) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) Alo Ahi m :=
  (fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing
    hβ).symm

end Exact3D
end StatMech
