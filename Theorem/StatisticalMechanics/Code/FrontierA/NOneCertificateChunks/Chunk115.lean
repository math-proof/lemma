/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk115.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk115


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts230_checked :
    rawMomentVCounts 230 = generatedVCounts230 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts230_checked :
    rawMomentQCounts 230 = generatedQCounts230 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients230_checked :
    rawMomentStateCoefficientList 230 = generatedStateCoefficients230 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts230_checked, qCounts230_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
