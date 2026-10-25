/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk018.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk018


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts36_checked :
    rawMomentVCounts 36 = generatedVCounts36 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts36_checked :
    rawMomentQCounts 36 = generatedQCounts36 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients36_checked :
    rawMomentStateCoefficientList 36 = generatedStateCoefficients36 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts36_checked, qCounts36_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
