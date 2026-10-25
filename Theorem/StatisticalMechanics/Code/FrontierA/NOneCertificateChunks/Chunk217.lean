/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk217.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk217


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts434_checked :
    rawMomentVCounts 434 = generatedVCounts434 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts434_checked :
    rawMomentQCounts 434 = generatedQCounts434 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients434_checked :
    rawMomentStateCoefficientList 434 = generatedStateCoefficients434 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts434_checked, qCounts434_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
