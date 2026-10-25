/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk245.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk245.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts491_checked :
    rawMomentVCounts 491 = generatedVCounts491 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts491_checked :
    rawMomentQCounts 491 = generatedQCounts491 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients491_checked :
    rawMomentStateCoefficientList 491 = generatedStateCoefficients491 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts491_checked, qCounts491_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
