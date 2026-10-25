/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk156.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk156


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts312_checked :
    rawMomentVCounts 312 = generatedVCounts312 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts312_checked :
    rawMomentQCounts 312 = generatedQCounts312 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients312_checked :
    rawMomentStateCoefficientList 312 = generatedStateCoefficients312 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts312_checked, qCounts312_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
