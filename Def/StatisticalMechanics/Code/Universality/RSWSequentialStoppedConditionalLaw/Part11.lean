/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorFoldRightHom {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (hypercubicLattice 2).induce
        (rlc_connectorAllowed gamma gamma' : Set (Site 2)) →g
      rlc_rightPathAvoidGraph gamma where
  toFun z := rlc_connectorFoldRight z
  map_rel' := by
    intro x y hxy
    refine ⟨rlc_connectorFoldRight_adj hxy,
      rlc_connectorFoldRight_mem_rect gamma gamma' x.2,
      rlc_connectorFoldRight_mem_rect gamma gamma' y.2,
      rlc_connectorFoldRight_not_path gamma gamma' x.2,
      rlc_connectorFoldRight_not_path gamma gamma' y.2⟩


noncomputable def rlc_connectorFoldLeftHom {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (hypercubicLattice 2).induce
        (rlc_connectorAllowed gamma gamma' : Set (Site 2)) →g
      rlc_leftPathAvoidGraph gamma' where
  toFun z := rlc_connectorFoldLeft z
  map_rel' := by
    intro x y hxy
    refine ⟨rlc_connectorFoldLeft_adj hxy,
      rlc_connectorFoldLeft_mem_rect gamma gamma' x.2,
      rlc_connectorFoldLeft_mem_rect gamma gamma' y.2,
      rlc_connectorFoldLeft_not_path gamma gamma' x.2,
      rlc_connectorFoldLeft_not_path gamma gamma' y.2⟩


end
end StatMech.Universality
