/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk173.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk173


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts346_checked :
    rawMomentVCounts 346 = generatedVCounts346 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts346_checked :
    rawMomentQCounts 346 = generatedQCounts346 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients346_checked :
    rawMomentStateCoefficientList 346 = generatedStateCoefficients346 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts346_checked, qCounts346_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
