/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk025.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts51_checked :
    rawMomentVCounts 51 = generatedVCounts51 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts51_checked :
    rawMomentQCounts 51 = generatedQCounts51 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients51_checked :
    rawMomentStateCoefficientList 51 = generatedStateCoefficients51 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts51_checked, qCounts51_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
