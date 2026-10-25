/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk085.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk085.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts171_checked :
    rawMomentVCounts 171 = generatedVCounts171 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts171_checked :
    rawMomentQCounts 171 = generatedQCounts171 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients171_checked :
    rawMomentStateCoefficientList 171 = generatedStateCoefficients171 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts171_checked, qCounts171_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
