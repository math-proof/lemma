/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk066.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk066.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts133_checked :
    rawMomentVCounts 133 = generatedVCounts133 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts133_checked :
    rawMomentQCounts 133 = generatedQCounts133 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients133_checked :
    rawMomentStateCoefficientList 133 = generatedStateCoefficients133 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts133_checked, qCounts133_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
