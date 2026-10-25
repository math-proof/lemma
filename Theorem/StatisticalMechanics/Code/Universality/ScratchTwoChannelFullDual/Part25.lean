/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part30
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullInnerOuterVertex_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') := by
  intro x y hxy
  apply Subtype.ext
  exact rlc_twoChannelIndexedOuterTarget_injective gamma gamma' hxy

theorem rlc_twoChannelFullInnerOuter_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch (rlc_twoChannelFullInnerGraph gamma gamma')
      (rlc_twoChannelIndexedOuterGraph gamma gamma')
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') := by
  intro x y
  exact rlc_twoChannelIndexedOuter_adjMatch gamma gamma' x.1 y.1


theorem rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    (hret : RlcTwoChannelIndexedRetainedEdge gamma gamma' f) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
      Set.range (FK.ocd_innerEdge
        (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
  let target := hret.choose
  induction ht : target.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (ht ▸ target.2)
      let x' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨x, Or.inr (Or.inr hxy.mem_support_left)⟩
      let y' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨y, Or.inr (Or.inr hxy.mem_support_right)⟩
      refine ⟨s(x', y'), ?_⟩
      rw [FK.ocd_innerEdge_mk]
      unfold rlc_twoChannelIndexedOuterEdge
      rw [dif_pos hret]
      simp [target, ht, x', y',
        rlc_twoChannelFullInnerOuterVertex,
        rlc_twoChannelIndexedOuterTarget]

theorem rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelIndexedOuterEdge gamma gamma'
        (rlc_twoChannelIndexedAugmentedEdge target) ∈
      Set.range (FK.ocd_innerEdge
        (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
  apply rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained
  exact ⟨target,
    (rlc_twoChannelIndexedAugmentedEdge_reflected target).symm⟩


end
end StatMech.Universality
