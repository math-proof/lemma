/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk182.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk182


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts364_checked :
    rawMomentVCounts 364 = generatedVCounts364 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts364_checked :
    rawMomentQCounts 364 = generatedQCounts364 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients364_checked :
    rawMomentStateCoefficientList 364 = generatedStateCoefficients364 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts364_checked, qCounts364_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
