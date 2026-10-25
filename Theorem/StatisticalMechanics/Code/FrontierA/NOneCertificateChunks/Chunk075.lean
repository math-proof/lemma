/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk075


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts150_checked :
    rawMomentVCounts 150 = generatedVCounts150 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts150_checked :
    rawMomentQCounts 150 = generatedQCounts150 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients150_checked :
    rawMomentStateCoefficientList 150 = generatedStateCoefficients150 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts150_checked, qCounts150_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
