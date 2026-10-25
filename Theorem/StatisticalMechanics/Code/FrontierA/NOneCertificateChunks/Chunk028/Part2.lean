/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk028.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk028.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts57_checked :
    rawMomentVCounts 57 = generatedVCounts57 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts57_checked :
    rawMomentQCounts 57 = generatedQCounts57 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients57_checked :
    rawMomentStateCoefficientList 57 = generatedStateCoefficients57 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts57_checked, qCounts57_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
