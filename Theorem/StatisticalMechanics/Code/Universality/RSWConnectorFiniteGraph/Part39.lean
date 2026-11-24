module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part57
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorInnerEdgeToVariable_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorInnerEdgeToVariable gamma gamma') := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val hef)

theorem rlc_connectorInnerEdgeToVariable_surjective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Surjective
      (rlc_connectorInnerEdgeToVariable gamma gamma') := by
  intro e
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y :=
        by
          have he := e.2
          rw [heq, SimpleGraph.mem_edgeSet] at he
          exact he
      let xc : RlcConnectorInnerVertex gamma gamma' :=
        ⟨x, Or.inr (Or.inr hxy.mem_support_left)⟩
      let yc : RlcConnectorInnerVertex gamma gamma' :=
        ⟨y, Or.inr (Or.inr hxy.mem_support_right)⟩
      let a : (rlc_connectorInnerGraph gamma gamma').edgeSet :=
        ⟨s(xc, yc), by
          rw [SimpleGraph.mem_edgeSet]
          exact hxy⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change s(x, y) = e.1
      exact heq.symm


end
end StatMech.Universality
