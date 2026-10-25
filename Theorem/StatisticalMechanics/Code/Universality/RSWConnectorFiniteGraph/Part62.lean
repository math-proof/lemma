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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part83
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorCollaredSplitOuterEventMass gamma gamma' p q A =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        rlc_connectorCollaredFibreWeight gamma gamma' p q xi *
          FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
            (rlc_connectorInnerCollaredInducedWiring gamma gamma'
              (rlc_connectorCollaredOuterStateOfSource
                gamma gamma' xi))
            (fun _ => p) q A := by
  unfold rlc_connectorCollaredSplitOuterEventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro xi _
  rw [show (∑ eta,
      A.indicator (fun _ => (1 : Real)) eta *
        FK.bcWeight
          (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorCollaredOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      FK.ocd_psiShift
          (rlc_connectorCollaredOuterDualGraph gamma gamma')
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)
          p q *
        FK.activeBCNumer (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerCollaredInducedWiring gamma gamma'
            (rlc_connectorCollaredOuterStateOfSource
              gamma gamma' xi))
          (fun _ => p) q (A.indicator fun _ => (1 : Real)) by
    unfold FK.activeBCNumer
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta _
    rw [rlc_connectorCollaredSplitSource_outerWeight]
    ring]
  unfold rlc_connectorCollaredFibreWeight FK.activeBCProbOf
  rw [FK.activeBCMean_eq_div]
  have hZi := (FK.activeBCZ_pos
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerCollaredInducedWiring gamma gamma'
      (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
    (fun _ => hp) (fun _ => hp1) hq).ne'
  field_simp

end
end StatMech.Universality
