/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexInfinityGraph (N n : Nat) : SimpleGraph (SixVertexSector N n) where
  Adj x y := x ≠ y ∧
    SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 * n
  symm := by
    constructor
    rintro x y ⟨hxy, hinter, hdist⟩
    exact ⟨Ne.symm hxy, (sixVertexInterlaced_comm _ _).mp hinter,
      (sixVertexRowDistance_comm _ _).symm.trans hdist⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩

end
end StatMech.FrontierD
