/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationComparisonExample.Part2


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationComparisonExample

open FinitePlusTailContractionExample

open FiniteWitnessPackageExample

open PackageReparameterizationBridgeExample

open FinitePlusTailHyperbolicSplitting

open InfiniteTailTableClosedBallRGPackage


theorem zeroTableClosedBallReparameterizedLength_pos :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      0 < zeroTableClosedBallReparameterizedLength β :=
  Filter.Eventually.of_forall fun _ => by
    dsimp [zeroTableClosedBallReparameterizedLength,
      halfThirdScalingCorrelationLength]
    exact Real.exp_pos _


theorem zeroTableClosedBallDoubledReparameterizedLength_comparable :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      (2 : ℝ) * zeroTableClosedBallReparameterizedLength β ≤
          zeroTableClosedBallDoubledReparameterizedLength β ∧
        zeroTableClosedBallDoubledReparameterizedLength β ≤
          (2 : ℝ) * zeroTableClosedBallReparameterizedLength β :=
  Filter.Eventually.of_forall fun β => by
    simp [zeroTableClosedBallDoubledReparameterizedLength,
      halfThirdScalingDoublePrefactor]


theorem zeroTableClosedBallRGPackage_bridge_doubled_reparameterized :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallDoubledReparameterizedLength :=
  zeroTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      exampleScale
      zeroTableClosedBallRGPackage_bridge_reparameterized
      zeroTableClosedBallReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      zeroTableClosedBallDoubledReparameterizedLength_comparable


theorem zeroTableClosedBallRGPackage_valid_doubled_reparameterized :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallDoubledReparameterizedLength :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_bridge_reparameterized
    zeroTableClosedBallReparameterizedLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    zeroTableClosedBallDoubledReparameterizedLength_comparable


theorem zeroTableClosedBallRGPackage_hasCriticalNu_doubled_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallDoubledReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_bridge_reparameterized
    zeroTableClosedBallReparameterizedLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    zeroTableClosedBallDoubledReparameterizedLength_comparable


end PackageReparameterizationComparisonExample
end Exact3D
end StatMech
