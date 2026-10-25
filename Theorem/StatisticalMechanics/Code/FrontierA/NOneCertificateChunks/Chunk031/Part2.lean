/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk031.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts63_checked :
    rawMomentVCounts 63 = generatedVCounts63 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts63_checked :
    rawMomentQCounts 63 = generatedQCounts63 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients63_checked :
    rawMomentStateCoefficientList 63 = generatedStateCoefficients63 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts63_checked, qCounts63_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
