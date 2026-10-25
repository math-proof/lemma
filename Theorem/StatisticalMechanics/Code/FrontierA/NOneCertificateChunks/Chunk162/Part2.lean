/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk162.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk162.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts325_checked :
    rawMomentVCounts 325 = generatedVCounts325 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts325_checked :
    rawMomentQCounts 325 = generatedQCounts325 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients325_checked :
    rawMomentStateCoefficientList 325 = generatedStateCoefficients325 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts325_checked, qCounts325_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
