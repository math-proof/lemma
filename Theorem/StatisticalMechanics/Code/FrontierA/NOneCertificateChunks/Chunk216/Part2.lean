/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk216.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk216.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts433_checked :
    rawMomentVCounts 433 = generatedVCounts433 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts433_checked :
    rawMomentQCounts 433 = generatedQCounts433 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients433_checked :
    rawMomentStateCoefficientList 433 = generatedStateCoefficients433 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts433_checked, qCounts433_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
