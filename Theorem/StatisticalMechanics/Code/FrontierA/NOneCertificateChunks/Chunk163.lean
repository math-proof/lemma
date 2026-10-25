/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk163.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk163


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts326_checked :
    rawMomentVCounts 326 = generatedVCounts326 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts326_checked :
    rawMomentQCounts 326 = generatedQCounts326 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients326_checked :
    rawMomentStateCoefficientList 326 = generatedStateCoefficients326 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts326_checked, qCounts326_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
