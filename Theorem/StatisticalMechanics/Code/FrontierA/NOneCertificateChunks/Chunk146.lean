/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk146.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk146


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts292_checked :
    rawMomentVCounts 292 = generatedVCounts292 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts292_checked :
    rawMomentQCounts 292 = generatedQCounts292 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients292_checked :
    rawMomentStateCoefficientList 292 = generatedStateCoefficients292 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts292_checked, qCounts292_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
