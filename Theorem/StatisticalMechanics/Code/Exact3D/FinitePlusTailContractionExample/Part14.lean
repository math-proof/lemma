/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part14


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingPrefactor_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingPrefactor β :=
  Filter.Eventually.of_forall fun _ => by
    norm_num [halfThirdScalingPrefactor]


theorem halfThirdScalingPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (halfThirdScalingPrefactor β) /
          Real.log (halfThirdScalingModel.betaC - β))
      (nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
  simp [halfThirdScalingPrefactor]


theorem halfThirdScalingDoublePrefactor_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingDoublePrefactor β :=
  Filter.Eventually.of_forall fun _ => by
    norm_num [halfThirdScalingDoublePrefactor]


theorem halfThirdScalingDoublePrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (halfThirdScalingDoublePrefactor β) /
          Real.log (halfThirdScalingModel.betaC - β))
      (nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
  let L := nhdsWithin halfThirdScalingModel.betaC
    (Set.Iio halfThirdScalingModel.betaC)
  have hlogd :
      Filter.Tendsto
        (fun β : ℝ => Real.log (halfThirdScalingModel.betaC - β))
        L Filter.atBot := by
    simpa [L] using tendsto_log_betaC_sub_atBot halfThirdScalingModel
  simpa [halfThirdScalingDoublePrefactor, L] using
    hlogd.const_div_atBot (Real.log (2 : ℝ))


theorem halfThirdScalingCorrelationLength_prefactor_power :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingCorrelationLength β =
        halfThirdScalingPrefactor β *
          Real.exp
            (-halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor]


end FinitePlusTailContractionExample
end Exact3D
end StatMech
