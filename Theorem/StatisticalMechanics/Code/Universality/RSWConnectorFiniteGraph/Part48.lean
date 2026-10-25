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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part66
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorFibreMixtureZ_eq_sum_outerWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorFibreMixtureZ gamma gamma' p q =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        ∑ eta : ConfigSpace
            (rlc_connectorInnerGraph gamma gamma').edgeSet,
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) := by
  unfold rlc_connectorFibreMixtureZ FK.activeBCZ
  apply Finset.sum_congr rfl
  intro xi _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorSplitSource_outerWeight]
  ring


end
end StatMech.Universality
