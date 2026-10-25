/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk117.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk117.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts235_checked :
    rawMomentVCounts 235 = generatedVCounts235 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts235_checked :
    rawMomentQCounts 235 = generatedQCounts235 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients235_checked :
    rawMomentStateCoefficientList 235 = generatedStateCoefficients235 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts235_checked, qCounts235_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
