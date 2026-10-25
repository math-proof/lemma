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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part16


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingMassPrefactor_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingMassPrefactor β :=
  Filter.Eventually.of_forall fun _ => by
    norm_num [halfThirdScalingMassPrefactor]


theorem halfThirdScalingMassPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (halfThirdScalingMassPrefactor β) /
          Real.log (halfThirdScalingModel.betaC - β))
      (nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
  simp [halfThirdScalingMassPrefactor]


theorem halfThirdScalingMass_power :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingMass β =
        halfThirdScalingMassPrefactor β *
          Real.exp
            (halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    simp [halfThirdScalingMass, halfThirdScalingMassPrefactor]


theorem halfThirdScalingCorrelationLength_eq_inv_mass :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingCorrelationLength β = (halfThirdScalingMass β)⁻¹ :=
  Filter.Eventually.of_forall fun β => by
    unfold halfThirdScalingCorrelationLength halfThirdScalingMass
    rw [show
        -halfThirdScalingRGCertificate.predictedExponent *
            Real.log (halfThirdScalingModel.betaC - β) =
          -(halfThirdScalingRGCertificate.predictedExponent *
            Real.log (halfThirdScalingModel.betaC - β)) by
        ring,
      Real.exp_neg]


end FinitePlusTailContractionExample
end Exact3D
end StatMech
