/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk158.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk158.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts317_checked :
    rawMomentVCounts 317 = generatedVCounts317 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts317_checked :
    rawMomentQCounts 317 = generatedQCounts317 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients317_checked :
    rawMomentStateCoefficientList 317 = generatedStateCoefficients317 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts317_checked, qCounts317_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
