/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk011.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts23_checked :
    rawMomentVCounts 23 = generatedVCounts23 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts23_checked :
    rawMomentQCounts 23 = generatedQCounts23 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients23_checked :
    rawMomentStateCoefficientList 23 = generatedStateCoefficients23 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts23_checked, qCounts23_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
