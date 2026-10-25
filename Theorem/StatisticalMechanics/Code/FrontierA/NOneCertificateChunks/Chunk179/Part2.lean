/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk179.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk179.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts359_checked :
    rawMomentVCounts 359 = generatedVCounts359 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts359_checked :
    rawMomentQCounts 359 = generatedQCounts359 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients359_checked :
    rawMomentStateCoefficientList 359 = generatedStateCoefficients359 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts359_checked, qCounts359_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
