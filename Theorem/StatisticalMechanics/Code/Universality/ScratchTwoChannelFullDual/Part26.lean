/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part31
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullIndexed_innerActive_eq_projection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.restrictActive (rlc_twoChannelFullInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) =
      rlc_twoChannelFullInnerActiveProjection gamma gamma' omega := by
  funext e
  unfold FK.restrictActive FK.ocd_innerRestrict
    rlc_twoChannelFullInnerActiveProjection
  rw [FK.ocd_innerEdge]
  have htarget : e.1.map Subtype.val ∈
      (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet := by
    induction he : e.1 using Sym2.inductionOn with
    | _ x y =>
        have hinner : (rlc_twoChannelFullInnerGraph gamma gamma').Adj
            x y := (SimpleGraph.mem_edgeSet _).mp (by
          rw [← he]
          exact e.2)
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
        exact hinner
  let target : RlcTwoChannelFullVariableTargetEdge gamma gamma' :=
    ⟨e.1.map Subtype.val, htarget⟩
  have hmap : e.1.map
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') =
      target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
    simp [target, rlc_twoChannelFullInnerOuterVertex,
      rlc_twoChannelIndexedOuterTarget, Sym2.map_map]
  rw [hmap]
  exact rlc_twoChannelIndexedOuterConfig_variable
    gamma gamma' omega target


theorem rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullInnerToVariable gamma gamma'
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) =
      rlc_twoChannelFullVariableProjection gamma gamma' omega := by
  funext target
  have hactive := congrFun
    (rlc_twoChannelFullIndexed_innerActive_eq_projection
      gamma gamma' omega)
    (rlc_twoChannelFullVariableTargetEdge_inner target)
  unfold FK.restrictActive
    rlc_twoChannelFullInnerActiveProjection at hactive
  unfold rlc_twoChannelFullInnerToVariable
    rlc_twoChannelFullVariableProjection at ⊢
  rw [rlc_twoChannelFullVariableTargetEdge_inner_map] at hactive
  exact hactive


end
end StatMech.Universality
