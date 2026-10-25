/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk091.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk091


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts182_checked :
    rawMomentVCounts 182 = generatedVCounts182 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts182_checked :
    rawMomentQCounts 182 = generatedQCounts182 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients182_checked :
    rawMomentStateCoefficientList 182 = generatedStateCoefficients182 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts182_checked, qCounts182_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
