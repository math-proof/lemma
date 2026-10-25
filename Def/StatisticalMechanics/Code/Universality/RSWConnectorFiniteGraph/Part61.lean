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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_connectorInnerActiveOfSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet :=
  fun e => !(tau (rlc_connectorInnerSourceEdge gamma gamma' e))


def rlc_connectorOuterActiveOfSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma') :=
  fun e => tau e.1


noncomputable def rlc_connectorSourceActiveAssemble {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (pair : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet ×
      ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
  fun e => if h : e ∈ Set.range
      (rlc_connectorInnerSourceEdge gamma gamma') then
    !(pair.1 h.choose)
  else pair.2 ⟨e, h⟩

end
end StatMech.Universality
