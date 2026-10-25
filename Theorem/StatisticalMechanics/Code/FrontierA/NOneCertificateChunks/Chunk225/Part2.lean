/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk225.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk225.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts451_checked :
    rawMomentVCounts 451 = generatedVCounts451 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts451_checked :
    rawMomentQCounts 451 = generatedQCounts451 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients451_checked :
    rawMomentStateCoefficientList 451 = generatedStateCoefficients451 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts451_checked, qCounts451_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
