/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelFullPhysicalCutTargetGraphAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n)) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
    target.1.1 = s(x, y) ∧
      ∃ u v : RlcConnectorVertex n,
        (rlc_twoChannelFullPhysicalSourceEdge target).1 = s(u, v) ∧
          ((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A))
  symm := by
    constructor
    rintro x y ⟨target, htarget, u, v, hsource, hcross⟩
    refine ⟨target, ?_, u, v, hsource, hcross⟩
    simpa [Sym2.eq_swap] using htarget
  loopless := ⟨fun x hxx => by
    obtain ⟨target, htarget, _u, _v, _hsource, _hcross⟩ := hxx
    have hbase : (rlc_connectorTwoChannelGraph gamma gamma').Adj x x := by
      rw [← SimpleGraph.mem_edgeSet, ← htarget]
      exact target.1.2
    exact hbase.ne rfl⟩


noncomputable def rlc_twoChannelFullPhysicalLiftVertexCut {n : Int}
    (A : Set (RlcConnectorVertex n)) : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect (-2 * n) (2 * n) (-n) n,
    (⟨z, hz⟩ : RlcConnectorVertex n) ∈ A}

end
end StatMech.Universality
