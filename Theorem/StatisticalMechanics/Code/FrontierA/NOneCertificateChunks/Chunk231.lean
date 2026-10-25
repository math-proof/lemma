/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk231.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk231


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts462_checked :
    rawMomentVCounts 462 = generatedVCounts462 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts462_checked :
    rawMomentQCounts 462 = generatedQCounts462 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients462_checked :
    rawMomentStateCoefficientList 462 = generatedStateCoefficients462 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts462_checked, qCounts462_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
