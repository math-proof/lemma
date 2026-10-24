/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoPositiveEvenAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity









namespace StatMech.FrontierD

theorem sixVertexFourByTwo_sectorTrace_logConcave_positiveEvenBase
    {c : Real} (hc : 2 <= c) :
    Matrix.trace
          (sixVertexSectorTransfer 4 0 c ^ sixVertexPositiveEvenHeight 0) *
        Matrix.trace
          (sixVertexSectorTransfer 4 2 c ^ sixVertexPositiveEvenHeight 0) <=
      Matrix.trace
          (sixVertexSectorTransfer 4 1 c ^ sixVertexPositiveEvenHeight 0) ^ 2 := by
  simpa [sixVertexPositiveEvenHeight] using
    sixVertexFourByTwo_sectorTrace_logConcave hc

end StatMech.FrontierD
