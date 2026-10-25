/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk210.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk210


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts420_checked :
    rawMomentVCounts 420 = generatedVCounts420 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts420_checked :
    rawMomentQCounts 420 = generatedQCounts420 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients420_checked :
    rawMomentStateCoefficientList 420 = generatedStateCoefficients420 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts420_checked, qCounts420_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
