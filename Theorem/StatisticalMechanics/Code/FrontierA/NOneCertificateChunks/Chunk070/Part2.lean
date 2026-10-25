/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk070.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk070.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts141_checked :
    rawMomentVCounts 141 = generatedVCounts141 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts141_checked :
    rawMomentQCounts 141 = generatedQCounts141 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients141_checked :
    rawMomentStateCoefficientList 141 = generatedStateCoefficients141 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts141_checked, qCounts141_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
