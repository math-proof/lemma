/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk151.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk151.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts303_checked :
    rawMomentVCounts 303 = generatedVCounts303 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts303_checked :
    rawMomentQCounts 303 = generatedQCounts303 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients303_checked :
    rawMomentStateCoefficientList 303 = generatedStateCoefficients303 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts303_checked, qCounts303_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
