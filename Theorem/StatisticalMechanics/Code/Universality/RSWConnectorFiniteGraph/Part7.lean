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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorForcedDualZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_connectorForcedDualZ gamma gamma' p q := by
  unfold rlc_connectorForcedDualZ
  exact Finset.sum_pos
    (fun tau _ => BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)) hp hp1 hq)
    Finset.univ_nonempty


theorem rlc_connectorForced_partition_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          rlc_connectorForcedDualZ gamma gamma'
            (BeffaraDC.dualParam p q) q := by
  dsimp only
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let t : Real := p ^
    (rlc_connectorTraceWiring gamma gamma').edgeFinset.card
  let A : Real := q ^ (P.G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
      q ^ Nat.card P.V
  unfold FK.bcZ rlc_connectorForcedDualZ
  calc
    t * (∑ tau, FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau) * A =
      ∑ tau, t * FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau * A := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ tau, B * BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
      apply Finset.sum_congr rfl
      intro tau _
      exact rlc_connectorForced_weight_duality gamma gamma' tau hp hp1 hq
    _ = B * ∑ tau, BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
      rw [Finset.mul_sum]


theorem rlc_bcProb_separate_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau =
      rlc_connectorForcedDualProb gamma gamma'
        (BeffaraDC.dualParam p q) q tau := by
  have hps0 : 0 < BeffaraDC.dualParam p q :=
    BeffaraDC.dualParam_pos hp hp1 hq
  have hps1 : BeffaraDC.dualParam p q < 1 :=
    BeffaraDC.dualParam_lt_one hp hp1 hq
  have hZp : FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') p q ≠ 0 :=
    (FK.bcZ_pos (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') hp hp1 hq).ne'
  have hZd : rlc_connectorForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q ≠ 0 :=
    (rlc_connectorForcedDualZ_pos gamma gamma' hps0 hps1 hq).ne'
  let C : Real :=
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
      q ^ ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card *
      q ^ Nat.card (rlc_connectorAugmentedPlanarDomain gamma gamma').V
  let wp := FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma') p q tau
  let wd := BeffaraDC.pfdDualWeight
    (rlc_connectorAugmentedPlanarDomain gamma gamma')
    (BeffaraDC.dualParam p q) q
    (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
      (rlc_connectorForceTraceConfig gamma gamma' tau))
  have hC : 0 < C := mul_pos (pow_pos hp _) (pow_pos hq _)
  have hB : 0 < B := by
    have hden : 0 < 1 - BeffaraDC.dualParam p q := by linarith
    exact mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)
  have hw : wp * C = B * wd := by
    have h := rlc_connectorForced_weight_duality
      gamma gamma' tau hp hp1 hq
    dsimp only at h
    dsimp only [wp, wd, C, B]
    nlinarith
  have hZ : FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q * C =
      B * rlc_connectorForcedDualZ gamma gamma'
        (BeffaraDC.dualParam p q) q := by
    have h := rlc_connectorForced_partition_duality
      gamma gamma' hp hp1 hq
    dsimp only at h
    dsimp only [C, B]
    nlinarith
  have hcross : wp * rlc_connectorForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q =
      wd * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q := by
    apply mul_left_cancel₀ hB.ne'
    calc
      B * (wp * rlc_connectorForcedDualZ gamma gamma'
          (BeffaraDC.dualParam p q) q) =
          wp * (B * rlc_connectorForcedDualZ gamma gamma'
            (BeffaraDC.dualParam p q) q) := by ring
      _ = wp * (FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q * C) := by rw [hZ]
      _ = (wp * C) * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q := by ring
      _ = (B * wd) * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q := by rw [hw]
      _ = B * (wd * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q) := by ring
  unfold FK.bcProb rlc_connectorForcedDualProb
  apply (div_eq_div_iff hZp hZd).2
  simpa only [wp, wd] using hcross


end
end StatMech.Universality
