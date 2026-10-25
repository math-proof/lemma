/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk076.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk076


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts152_checked :
    rawMomentVCounts 152 = generatedVCounts152 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts152_checked :
    rawMomentQCounts 152 = generatedQCounts152 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients152_checked :
    rawMomentStateCoefficientList 152 = generatedStateCoefficients152 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts152_checked, qCounts152_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
