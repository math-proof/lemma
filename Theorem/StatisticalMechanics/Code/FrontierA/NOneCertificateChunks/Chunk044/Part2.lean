/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk044.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk044.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts89_checked :
    rawMomentVCounts 89 = generatedVCounts89 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts89_checked :
    rawMomentQCounts 89 = generatedQCounts89 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients89_checked :
    rawMomentStateCoefficientList 89 = generatedStateCoefficients89 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts89_checked, qCounts89_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
