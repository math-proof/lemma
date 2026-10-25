/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk171.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk171.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts343_checked :
    rawMomentVCounts 343 = generatedVCounts343 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts343_checked :
    rawMomentQCounts 343 = generatedQCounts343 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients343_checked :
    rawMomentStateCoefficientList 343 = generatedStateCoefficients343 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts343_checked, qCounts343_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
