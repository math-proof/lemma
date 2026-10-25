/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part7
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexFiniteTorusRowPartitionSum_eq_sum_sector_traces
    (T : EvenTorus) (c : ℝ) :
    sixVertexFiniteTorusRowPartitionSum T c =
      ∑ n : Fin (T.width + 1),
        Matrix.trace (sixVertexSectorTransfer T.width n c ^ T.height) := by
  exact sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces
    T.width T.height T.height_pos c

end StatMech.FrontierD
