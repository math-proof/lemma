/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Def.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part4
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta
    {β A mass : ℝ} (hβpos : 0 < β)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  simpa [freeInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkExactFreeIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) hexact


theorem fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta
    {β A mass : ℝ} (hβpos : 0 < β)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  simpa [wiredInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkExactWiredIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) hexact


theorem fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  rcases hsubexp with ⟨hA_pos, hA_log, hvalues⟩
  simpa [freeInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hA_pos hA_log hvalues


theorem fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  rcases hsubexp with ⟨hA_pos, hA_log, hvalues⟩
  simpa [wiredInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hA_pos hA_log hvalues


end Exact3D
end StatMech
