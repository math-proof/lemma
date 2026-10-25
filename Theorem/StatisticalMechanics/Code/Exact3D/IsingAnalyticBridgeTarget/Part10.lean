/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part4


namespace StatMech

namespace Exact3D

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem free_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) :=
  T.free_realizesXAxisLength β hβ


theorem plus_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) :=
  plus_hasCorrelationLength_xAxis_of_free_agree T.plus_free_agree hβ.2
    (T.free_realizesXAxisLength β hβ)


theorem eventually_mem_leftCriticalInterval
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos


theorem eventually_betaC_sub_lt_delta
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos


theorem eventually_free_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.free_hasCorrelationLength hβ


theorem eventually_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.plus_hasCorrelationLength hβ


theorem eventually_prefactor_pos
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ


theorem eventually_length_scaling
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        T.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling β hβ


end FreeAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech
