/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk206.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk206


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts412_checked :
    rawMomentVCounts 412 = generatedVCounts412 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts412_checked :
    rawMomentQCounts 412 = generatedQCounts412 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients412_checked :
    rawMomentStateCoefficientList 412 = generatedStateCoefficients412 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts412_checked, qCounts412_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
