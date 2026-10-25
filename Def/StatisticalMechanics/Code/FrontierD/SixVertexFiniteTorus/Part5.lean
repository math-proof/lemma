/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part3
open Finset Matrix


namespace StatMech.FrontierD

def sixVertexPeriodicSectorIndex {N M : ℕ} {hM : 0 < M} {c : ℝ}
    (x : SixVertexPeriodicRows N M hM c) : Fin (N + 1) :=
  ⟨sixVertexUpCount (x.1 ⟨0, hM⟩), by
    have hcard := Finset.card_le_univ ({i | x.1 ⟨0, hM⟩ i} : Finset (Fin N))
    simpa [sixVertexUpCount] using Nat.lt_succ_of_le hcard⟩


end StatMech.FrontierD
