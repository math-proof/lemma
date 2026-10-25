/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk098.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk098


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts196_checked :
    rawMomentVCounts 196 = generatedVCounts196 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts196_checked :
    rawMomentQCounts 196 = generatedQCounts196 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients196_checked :
    rawMomentStateCoefficientList 196 = generatedStateCoefficients196 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts196_checked, qCounts196_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
