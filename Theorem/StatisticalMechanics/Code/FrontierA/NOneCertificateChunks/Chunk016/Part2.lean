/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk016.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts33_checked :
    rawMomentVCounts 33 = generatedVCounts33 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts33_checked :
    rawMomentQCounts 33 = generatedQCounts33 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients33_checked :
    rawMomentStateCoefficientList 33 = generatedStateCoefficients33 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts33_checked, qCounts33_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
