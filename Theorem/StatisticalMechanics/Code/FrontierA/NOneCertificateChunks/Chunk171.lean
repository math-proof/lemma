/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk171.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk171


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts342_checked :
    rawMomentVCounts 342 = generatedVCounts342 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts342_checked :
    rawMomentQCounts 342 = generatedQCounts342 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients342_checked :
    rawMomentStateCoefficientList 342 = generatedStateCoefficients342 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts342_checked, qCounts342_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
