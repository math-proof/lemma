/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk226.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk226


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts452_checked :
    rawMomentVCounts 452 = generatedVCounts452 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts452_checked :
    rawMomentQCounts 452 = generatedQCounts452 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients452_checked :
    rawMomentStateCoefficientList 452 = generatedStateCoefficients452 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts452_checked, qCounts452_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
