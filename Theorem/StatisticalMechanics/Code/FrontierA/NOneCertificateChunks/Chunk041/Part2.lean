/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk041.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts83_checked :
    rawMomentVCounts 83 = generatedVCounts83 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts83_checked :
    rawMomentQCounts 83 = generatedQCounts83 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients83_checked :
    rawMomentStateCoefficientList 83 = generatedStateCoefficients83 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts83_checked, qCounts83_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
