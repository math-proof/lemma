/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk129.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk129.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts259_checked :
    rawMomentVCounts 259 = generatedVCounts259 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts259_checked :
    rawMomentQCounts 259 = generatedQCounts259 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients259_checked :
    rawMomentStateCoefficientList 259 = generatedStateCoefficients259 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts259_checked, qCounts259_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
