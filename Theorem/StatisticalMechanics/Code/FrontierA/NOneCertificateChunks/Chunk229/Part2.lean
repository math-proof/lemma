/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk229.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk229.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts459_checked :
    rawMomentVCounts 459 = generatedVCounts459 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts459_checked :
    rawMomentQCounts 459 = generatedQCounts459 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients459_checked :
    rawMomentStateCoefficientList 459 = generatedStateCoefficients459 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts459_checked, qCounts459_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
