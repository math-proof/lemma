/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk032


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts64_checked :
    rawMomentVCounts 64 = generatedVCounts64 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts64_checked :
    rawMomentQCounts 64 = generatedQCounts64 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients64_checked :
    rawMomentStateCoefficientList 64 = generatedStateCoefficients64 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts64_checked, qCounts64_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
