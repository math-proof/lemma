/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk199.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk199.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts399_checked :
    rawMomentVCounts 399 = generatedVCounts399 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts399_checked :
    rawMomentQCounts 399 = generatedQCounts399 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients399_checked :
    rawMomentStateCoefficientList 399 = generatedStateCoefficients399 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts399_checked, qCounts399_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
