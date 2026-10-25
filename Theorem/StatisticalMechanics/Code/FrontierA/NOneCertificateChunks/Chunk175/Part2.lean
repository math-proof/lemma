/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk175.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk175.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts351_checked :
    rawMomentVCounts 351 = generatedVCounts351 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts351_checked :
    rawMomentQCounts 351 = generatedQCounts351 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients351_checked :
    rawMomentStateCoefficientList 351 = generatedStateCoefficients351 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts351_checked, qCounts351_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
