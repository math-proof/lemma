/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part43
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorOuterFaceTag_eq_true_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    rlc_connectorOuterFaceTag gamma gamma' x = true ↔
      RlcConnectorOuterIsFace gamma gamma' x := by
  rcases x with x | (x | x) <;>
    simp [rlc_connectorOuterFaceTag, RlcConnectorOuterIsFace]


@[simp] theorem rlc_connectorOuterFaceTag_outerDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    (rlc_connectorOuterDualEdge gamma gamma' f).map
        (rlc_connectorOuterFaceTag gamma gamma') = s(false, false) := by
  unfold rlc_connectorOuterDualEdge
  split
  · rename_i hret
    induction hret.choose.1 using Sym2.inductionOn with
    | _ x y =>
        simp [rlc_connectorOuterTargetVertex,
          rlc_connectorOuterFaceTag]
  · simp [rlc_connectorOuterPort, rlc_connectorOuterFaceTag]

theorem rlc_connectorOuterSpoke_faceTag_ne_false {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : (rlc_connectorOuterSpokeGraph gamma gamma').Adj x y) :
    s(x, y).map (rlc_connectorOuterFaceTag gamma gamma') ≠
      s(false, false) := by
  intro htag
  rw [Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_connectorOuterFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_connectorOuterFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  rcases hxy.2.2 with hx | hy
  · have := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [this] at hxfalse
  · have := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [this] at hyfalse


theorem rlc_connectorOuterDualEdge_not_mem_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∉
      (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet := by
  induction hxy : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      intro hspoke
      apply rlc_connectorOuterSpoke_faceTag_ne_false gamma gamma' hspoke
      rw [← hxy]
      exact rlc_connectorOuterFaceTag_outerDualEdge gamma gamma' f


end
end StatMech.Universality
