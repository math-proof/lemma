/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk236.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk236.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts473_checked :
    rawMomentVCounts 473 = generatedVCounts473 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts473_checked :
    rawMomentQCounts 473 = generatedQCounts473 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients473_checked :
    rawMomentStateCoefficientList 473 = generatedStateCoefficients473 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts473_checked, qCounts473_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
