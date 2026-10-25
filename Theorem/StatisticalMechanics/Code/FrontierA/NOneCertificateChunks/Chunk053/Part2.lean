/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk053.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk053.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts107_checked :
    rawMomentVCounts 107 = generatedVCounts107 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts107_checked :
    rawMomentQCounts 107 = generatedQCounts107 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients107_checked :
    rawMomentStateCoefficientList 107 = generatedStateCoefficients107 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts107_checked, qCounts107_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
