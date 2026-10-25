/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk073.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk073.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts147_checked :
    rawMomentVCounts 147 = generatedVCounts147 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts147_checked :
    rawMomentQCounts 147 = generatedQCounts147 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients147_checked :
    rawMomentStateCoefficientList 147 = generatedStateCoefficients147 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts147_checked, qCounts147_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
