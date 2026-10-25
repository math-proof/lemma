/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk058.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk058.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts117_checked :
    rawMomentVCounts 117 = generatedVCounts117 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts117_checked :
    rawMomentQCounts 117 = generatedQCounts117 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients117_checked :
    rawMomentStateCoefficientList 117 = generatedStateCoefficients117 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts117_checked, qCounts117_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
