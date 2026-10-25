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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part61
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorSourceActiveAssemble_inner {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi)
        (rlc_connectorInnerSourceEdge gamma gamma' e) = !(eta e) := by
  unfold rlc_connectorSourceActiveAssemble
  split
  · rename_i h
    have he : h.choose = e :=
      rlc_connectorInnerSourceEdge_injective gamma gamma' h.choose_spec
    rw [he]
  · rename_i h
    exact (h ⟨e, rfl⟩).elim

@[simp] theorem rlc_connectorSourceActiveAssemble_outer {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (e : RlcConnectorOuterSourceEdge gamma gamma') :
    rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) e.1 = xi e := by
  unfold rlc_connectorSourceActiveAssemble
  rw [dif_neg e.2]


end
end StatMech.Universality
