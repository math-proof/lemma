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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part34
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorInnerCollaredInducedWiring_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi phi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))}
    (hpsi : psi ≤ phi) :
    rlc_connectorInnerCollaredInducedWiring gamma gamma' psi ≤
      rlc_connectorInnerCollaredInducedWiring gamma gamma' phi := by
  intro x y hxy
  refine ⟨hxy.1, hxy.2.mono ?_⟩
  intro u v huv
  rw [FK.ocd_outsideGraph_adj] at huv ⊢
  rcases huv with hopen | hboundary
  · exact Or.inl ⟨hopen.1, hpsi _ hopen.2.1, hopen.2.2⟩
  · exact Or.inr hboundary

theorem rlc_connectorInnerCollaredInducedWiring_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorInnerCollaredInducedWiring gamma gamma'
        (rlc_connectorCollaredOuterDualConfig gamma gamma' tau) ≤
      rlc_connectorInnerCollaredMaxInducedWiring gamma gamma' := by
  exact rlc_connectorInnerCollaredInducedWiring_mono gamma gamma'
    (rlc_connectorCollaredOuterDualConfig_le_max gamma gamma' tau)


theorem rlc_connector_activeBCProbOf_q_one_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (pf : Sym2 V → Real) (A : Set (ConfigSpace G.edgeSet)) :
    FK.activeBCProbOf G C pf 1 A =
      FK.activeBCProbOf G D pf 1 A := by
  unfold FK.activeBCProbOf FK.activeBCMean FK.activeBCProb
    FK.activeBCZ FK.activeBCWeight
  simp only [one_pow, mul_one]


theorem rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorSplitOuterEventMass gamma gamma' p 1 A =
      FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerMergedWiring gamma gamma')
        (fun _ => p) 1 A := by
  rw [rlc_connectorSplitOuterEventMass_eq_fibreMixture
    gamma gamma' hp hp1 zero_lt_one]
  simp_rw [rlc_connector_activeBCProbOf_q_one_independent
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerInducedWiring gamma gamma'
      (rlc_connectorOuterStateOfSource gamma gamma' _))
    (rlc_connectorInnerMergedWiring gamma gamma')]
  rw [← Finset.sum_mul,
    rlc_connectorFibreWeight_sum_eq_one
      gamma gamma' hp hp1 zero_lt_one, one_mul]


theorem rlc_connectorCollaredSplitOuterEventMass_q_one_eq_innerMerged
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorCollaredSplitOuterEventMass gamma gamma' p 1 A =
      FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerMergedWiring gamma gamma')
        (fun _ => p) 1 A := by
  rw [rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture
    gamma gamma' hp hp1 zero_lt_one]
  simp_rw [rlc_connector_activeBCProbOf_q_one_independent
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerCollaredInducedWiring gamma gamma'
      (rlc_connectorCollaredOuterStateOfSource gamma gamma' _))
    (rlc_connectorInnerMergedWiring gamma gamma')]
  rw [← Finset.sum_mul,
    rlc_connectorCollaredFibreWeight_sum_eq_one
      gamma gamma' hp hp1 zero_lt_one, one_mul]


theorem rlc_connectorForcedDualReducedEventMass_q_one_eq_innerMerged
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorForcedDualEventMass gamma gamma' p 1
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A) =
      FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerMergedWiring gamma gamma')
        (fun _ => p) 1 A := by
  rw [rlc_connectorForcedDualReducedEventMass_eq_split
    gamma gamma' hp,
    rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged
      gamma gamma' hp hp1]


end
end StatMech.Universality
