/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk072.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk072.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts145_checked :
    rawMomentVCounts 145 = generatedVCounts145 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts145_checked :
    rawMomentQCounts 145 = generatedQCounts145 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients145_checked :
    rawMomentStateCoefficientList 145 = generatedStateCoefficients145 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts145_checked, qCounts145_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
