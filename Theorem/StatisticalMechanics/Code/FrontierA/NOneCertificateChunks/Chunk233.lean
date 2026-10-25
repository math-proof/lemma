/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk233.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk233


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts466_checked :
    rawMomentVCounts 466 = generatedVCounts466 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts466_checked :
    rawMomentQCounts 466 = generatedQCounts466 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients466_checked :
    rawMomentStateCoefficientList 466 = generatedStateCoefficients466 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts466_checked, qCounts466_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
