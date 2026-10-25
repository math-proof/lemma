/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk152.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk152.Part3


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem coefficientChunk152_checked :
    rawMomentCoefficientSmallList 304 2 = generatedCoefficientChunk152 := by
  unfold rawMomentCoefficientSmallList
  change addCoefficientLists
    (addCoefficientLists (List.replicate 800 0)
      (rawMomentStateCoefficientList 304))
    (rawMomentStateCoefficientList 305) = generatedCoefficientChunk152
  rw [stateCoefficients304_checked, stateCoefficients305_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
