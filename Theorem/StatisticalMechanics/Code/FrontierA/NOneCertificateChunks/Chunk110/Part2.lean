/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk110.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts221_checked :
    rawMomentVCounts 221 = generatedVCounts221 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts221_checked :
    rawMomentQCounts 221 = generatedQCounts221 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients221_checked :
    rawMomentStateCoefficientList 221 = generatedStateCoefficients221 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts221_checked, qCounts221_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
