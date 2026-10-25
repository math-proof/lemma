/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk176.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk176


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts352_checked :
    rawMomentVCounts 352 = generatedVCounts352 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts352_checked :
    rawMomentQCounts 352 = generatedQCounts352 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients352_checked :
    rawMomentStateCoefficientList 352 = generatedStateCoefficients352 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts352_checked, qCounts352_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
