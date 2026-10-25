/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk073.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk073


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts146_checked :
    rawMomentVCounts 146 = generatedVCounts146 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts146_checked :
    rawMomentQCounts 146 = generatedQCounts146 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients146_checked :
    rawMomentStateCoefficientList 146 = generatedStateCoefficients146 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts146_checked, qCounts146_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
