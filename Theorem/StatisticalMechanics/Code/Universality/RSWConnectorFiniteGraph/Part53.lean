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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part28
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorInnerInducedWiring_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi phi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))}
    (hpsi : psi ≤ phi) :
    rlc_connectorInnerInducedWiring gamma gamma' psi ≤
      rlc_connectorInnerInducedWiring gamma gamma' phi := by
  intro x y hxy
  refine ⟨hxy.1, hxy.2.mono ?_⟩
  intro u v huv
  rw [FK.ocd_outsideGraph_adj] at huv ⊢
  rcases huv with hopen | hboundary
  · exact Or.inl ⟨hopen.1, hpsi _ hopen.2.1, hopen.2.2⟩
  · exact Or.inr hboundary


theorem rlc_connectorInnerInducedWiring_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorInnerInducedWiring gamma gamma'
        (rlc_connectorOuterDualConfig gamma gamma' tau) ≤
      rlc_connectorInnerMaxInducedWiring gamma gamma' := by
  exact rlc_connectorInnerInducedWiring_mono gamma gamma'
    (rlc_connectorOuterDualConfig_le_max gamma gamma' tau)


end
end StatMech.Universality
