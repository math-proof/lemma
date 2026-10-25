/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk087.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk087.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts175_checked :
    rawMomentVCounts 175 = generatedVCounts175 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts175_checked :
    rawMomentQCounts 175 = generatedQCounts175 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients175_checked :
    rawMomentStateCoefficientList 175 = generatedStateCoefficients175 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts175_checked, qCounts175_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
