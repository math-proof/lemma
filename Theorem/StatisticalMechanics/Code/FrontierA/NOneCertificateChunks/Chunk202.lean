/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk202.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk202


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts404_checked :
    rawMomentVCounts 404 = generatedVCounts404 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts404_checked :
    rawMomentQCounts 404 = generatedQCounts404 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients404_checked :
    rawMomentStateCoefficientList 404 = generatedStateCoefficients404 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts404_checked, qCounts404_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
