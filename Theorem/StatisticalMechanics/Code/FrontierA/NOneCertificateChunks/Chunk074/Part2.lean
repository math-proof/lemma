/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk074.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk074.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts149_checked :
    rawMomentVCounts 149 = generatedVCounts149 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts149_checked :
    rawMomentQCounts 149 = generatedQCounts149 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients149_checked :
    rawMomentStateCoefficientList 149 = generatedStateCoefficients149 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts149_checked, qCounts149_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
