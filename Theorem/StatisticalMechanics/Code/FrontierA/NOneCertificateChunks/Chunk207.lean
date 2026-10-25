/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk207.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk207


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts414_checked :
    rawMomentVCounts 414 = generatedVCounts414 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts414_checked :
    rawMomentQCounts 414 = generatedQCounts414 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients414_checked :
    rawMomentStateCoefficientList 414 = generatedStateCoefficients414 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts414_checked, qCounts414_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
