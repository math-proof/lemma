/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk203.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk203.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts407_checked :
    rawMomentVCounts 407 = generatedVCounts407 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts407_checked :
    rawMomentQCounts 407 = generatedQCounts407 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients407_checked :
    rawMomentStateCoefficientList 407 = generatedStateCoefficients407 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts407_checked, qCounts407_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
