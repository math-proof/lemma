/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk059.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk059.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts119_checked :
    rawMomentVCounts 119 = generatedVCounts119 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts119_checked :
    rawMomentQCounts 119 = generatedQCounts119 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients119_checked :
    rawMomentStateCoefficientList 119 = generatedStateCoefficients119 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts119_checked, qCounts119_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
