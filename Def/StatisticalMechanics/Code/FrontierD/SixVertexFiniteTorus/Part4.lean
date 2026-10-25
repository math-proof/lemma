/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexPeriodicRowWeight {N M : ℕ} (hM : 0 < M) (c : ℝ)
    (x : SixVertexPeriodicRows N M hM c) : ℝ :=
  matrixCycleWeight hM (sixVertexTransfer N c) x


noncomputable def sixVertexPeriodicRowPartitionSum
    (N M : ℕ) (hM : 0 < M) (c : ℝ) : ℝ :=
  ∑ x : SixVertexPeriodicRows N M hM c,
    sixVertexPeriodicRowWeight hM c x

def sixVertexRowInSector {N n : ℕ} (x : SixVertexRow N)
    (h : sixVertexUpCount x = n) : SixVertexSector N n :=
  ⟨({i | x i} : Finset (Fin N)), by simpa [sixVertexUpCount] using h⟩

end StatMech.FrontierD
