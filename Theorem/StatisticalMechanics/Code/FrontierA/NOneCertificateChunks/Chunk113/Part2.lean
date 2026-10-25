/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk113.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk113.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts227_checked :
    rawMomentVCounts 227 = generatedVCounts227 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts227_checked :
    rawMomentQCounts 227 = generatedQCounts227 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients227_checked :
    rawMomentStateCoefficientList 227 = generatedStateCoefficients227 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts227_checked, qCounts227_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
