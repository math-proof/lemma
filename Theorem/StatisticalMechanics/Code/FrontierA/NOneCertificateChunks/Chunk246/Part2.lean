/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk246.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk246.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts493_checked :
    rawMomentVCounts 493 = generatedVCounts493 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts493_checked :
    rawMomentQCounts 493 = generatedQCounts493 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients493_checked :
    rawMomentStateCoefficientList 493 = generatedStateCoefficients493 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts493_checked, qCounts493_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
