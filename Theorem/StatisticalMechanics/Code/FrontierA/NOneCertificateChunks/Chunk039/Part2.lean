/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk039.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk039.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts79_checked :
    rawMomentVCounts 79 = generatedVCounts79 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts79_checked :
    rawMomentQCounts 79 = generatedQCounts79 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients79_checked :
    rawMomentStateCoefficientList 79 = generatedStateCoefficients79 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts79_checked, qCounts79_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
