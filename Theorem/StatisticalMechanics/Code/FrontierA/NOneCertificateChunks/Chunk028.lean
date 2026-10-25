/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk028.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk028


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts56_checked :
    rawMomentVCounts 56 = generatedVCounts56 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts56_checked :
    rawMomentQCounts 56 = generatedQCounts56 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients56_checked :
    rawMomentStateCoefficientList 56 = generatedStateCoefficients56 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts56_checked, qCounts56_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
