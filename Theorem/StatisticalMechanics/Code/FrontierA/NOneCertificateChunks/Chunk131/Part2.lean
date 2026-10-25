/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk131.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk131.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts263_checked :
    rawMomentVCounts 263 = generatedVCounts263 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts263_checked :
    rawMomentQCounts 263 = generatedQCounts263 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients263_checked :
    rawMomentStateCoefficientList 263 = generatedStateCoefficients263 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts263_checked, qCounts263_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
