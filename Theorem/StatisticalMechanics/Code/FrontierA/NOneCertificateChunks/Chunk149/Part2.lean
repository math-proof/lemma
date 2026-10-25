/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk149.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk149.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts299_checked :
    rawMomentVCounts 299 = generatedVCounts299 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts299_checked :
    rawMomentQCounts 299 = generatedQCounts299 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients299_checked :
    rawMomentStateCoefficientList 299 = generatedStateCoefficients299 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts299_checked, qCounts299_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
