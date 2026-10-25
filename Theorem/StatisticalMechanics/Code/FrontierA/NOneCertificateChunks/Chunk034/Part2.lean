/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk034.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk034.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts69_checked :
    rawMomentVCounts 69 = generatedVCounts69 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts69_checked :
    rawMomentQCounts 69 = generatedQCounts69 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients69_checked :
    rawMomentStateCoefficientList 69 = generatedStateCoefficients69 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts69_checked, qCounts69_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
