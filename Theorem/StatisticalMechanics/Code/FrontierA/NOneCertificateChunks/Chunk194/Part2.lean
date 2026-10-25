/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk194.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk194.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts389_checked :
    rawMomentVCounts 389 = generatedVCounts389 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts389_checked :
    rawMomentQCounts 389 = generatedQCounts389 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients389_checked :
    rawMomentStateCoefficientList 389 = generatedStateCoefficients389 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts389_checked, qCounts389_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
