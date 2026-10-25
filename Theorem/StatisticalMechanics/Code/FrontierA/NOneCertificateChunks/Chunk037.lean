/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk037.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk037


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts74_checked :
    rawMomentVCounts 74 = generatedVCounts74 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts74_checked :
    rawMomentQCounts 74 = generatedQCounts74 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients74_checked :
    rawMomentStateCoefficientList 74 = generatedStateCoefficients74 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts74_checked, qCounts74_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
