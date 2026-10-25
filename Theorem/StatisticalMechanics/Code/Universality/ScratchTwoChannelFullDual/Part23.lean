/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullVariableTargetEdge_inner_exists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    ∃ e : (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet,
      e.1.map Subtype.val = target.1 := by
  induction ht : target.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (ht ▸ target.2)
      let x' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨x, Or.inr (Or.inr hxy.mem_support_left)⟩
      let y' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨y, Or.inr (Or.inr hxy.mem_support_right)⟩
      let e : (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet :=
        ⟨s(x', y'), (SimpleGraph.mem_edgeSet _).mpr hxy⟩
      exact ⟨e, by simp [e, x', y', ht]⟩


end
end StatMech.Universality
