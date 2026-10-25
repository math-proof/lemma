/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk049.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk049.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts99_checked :
    rawMomentVCounts 99 = generatedVCounts99 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts99_checked :
    rawMomentQCounts 99 = generatedQCounts99 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients99_checked :
    rawMomentStateCoefficientList 99 = generatedStateCoefficients99 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts99_checked, qCounts99_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
