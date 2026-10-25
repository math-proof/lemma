/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk048


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts96_checked :
    rawMomentVCounts 96 = generatedVCounts96 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts96_checked :
    rawMomentQCounts 96 = generatedQCounts96 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients96_checked :
    rawMomentStateCoefficientList 96 = generatedStateCoefficients96 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts96_checked, qCounts96_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
