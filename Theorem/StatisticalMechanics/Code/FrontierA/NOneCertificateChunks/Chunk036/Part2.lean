/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk036.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk036.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts73_checked :
    rawMomentVCounts 73 = generatedVCounts73 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts73_checked :
    rawMomentQCounts 73 = generatedQCounts73 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients73_checked :
    rawMomentStateCoefficientList 73 = generatedStateCoefficients73 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts73_checked, qCounts73_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
