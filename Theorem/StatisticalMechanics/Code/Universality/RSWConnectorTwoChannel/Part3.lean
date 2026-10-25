/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelForcedDualZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_twoChannelForcedDualZ gamma gamma' p q := by
  unfold rlc_twoChannelForcedDualZ
  exact Finset.sum_pos
    (fun rho _ => BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho)) hp hp1 hq)
    Finset.univ_nonempty

theorem rlc_twoChannelForced_partition_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          rlc_twoChannelForcedDualZ gamma gamma'
            (BeffaraDC.dualParam p q) q := by
  dsimp only
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let t : Real := p ^
    (rlc_connectorTraceWiring gamma gamma').edgeFinset.card
  let A : Real := q ^ (P.G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
      q ^ Nat.card P.V
  unfold FK.bcZ rlc_twoChannelForcedDualZ
  calc
    t * (∑ rho, FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho) * A =
      ∑ rho, t * FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho * A := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ rho, B * BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
      apply Finset.sum_congr rfl
      intro rho _
      exact rlc_twoChannelForced_weight_duality
        gamma gamma' rho hp hp1 hq
    _ = B * ∑ rho, BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
      rw [Finset.mul_sum]

theorem rlc_twoChannel_bcProb_separate_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho =
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.dualParam p q) q rho := by
  have hps0 : 0 < BeffaraDC.dualParam p q :=
    BeffaraDC.dualParam_pos hp hp1 hq
  have hps1 : BeffaraDC.dualParam p q < 1 :=
    BeffaraDC.dualParam_lt_one hp hp1 hq
  have hZp : FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') p q ≠ 0 :=
    (FK.bcZ_pos (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') hp hp1 hq).ne'
  have hZd : rlc_twoChannelForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q ≠ 0 :=
    (rlc_twoChannelForcedDualZ_pos gamma gamma' hps0 hps1 hq).ne'
  let C : Real :=
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
      q ^ ((rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^
        (rlc_connectorTwoChannelAugmentedPlanarDomain
          gamma gamma').G.edgeFinset.card *
      q ^ Nat.card
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').V
  let wp := FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma') p q rho
  let wd := BeffaraDC.pfdDualWeight
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
    (BeffaraDC.dualParam p q) q
    (FK.openSub
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
      (rlc_connectorForceTraceConfig gamma gamma' rho))
  have hC : 0 < C := mul_pos (pow_pos hp _) (pow_pos hq _)
  have hB : 0 < B := by
    have hden : 0 < 1 - BeffaraDC.dualParam p q := by linarith
    exact mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)
  have hw : wp * C = B * wd := by
    have h := rlc_twoChannelForced_weight_duality
      gamma gamma' rho hp hp1 hq
    dsimp only at h
    dsimp only [wp, wd, C, B]
    calc
      _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q rho *
          q ^ ((rlc_connectorTwoChannelAugmentedPlanarDomain
            gamma gamma').G.edgeFinset.card + 1) := by ring
      _ = _ := h
  have hZ : FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q * C =
      B * rlc_twoChannelForcedDualZ gamma gamma'
        (BeffaraDC.dualParam p q) q := by
    have h := rlc_twoChannelForced_partition_duality
      gamma gamma' hp hp1 hq
    dsimp only at h
    dsimp only [C, B]
    calc
      _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q *
          q ^ ((rlc_connectorTwoChannelAugmentedPlanarDomain
            gamma gamma').G.edgeFinset.card + 1) := by ring
      _ = _ := h
  have hcrossCB :
      C * (B * (wp * rlc_twoChannelForcedDualZ gamma gamma'
        (BeffaraDC.dualParam p q) q)) =
      C * (B * (wd * FK.bcZ
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q)) := by
    calc
      C * (B * (wp * rlc_twoChannelForcedDualZ gamma gamma'
          (BeffaraDC.dualParam p q) q)) =
        (wp * C) * (B * rlc_twoChannelForcedDualZ gamma gamma'
          (BeffaraDC.dualParam p q) q) := by ring
      _ = (B * wd) *
          (FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q * C) := by
        rw [hw, hZ]
      _ = C * (B * (wd * FK.bcZ
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q)) := by ring
  have hcrossB := mul_left_cancel₀ hC.ne' hcrossCB
  have hcross : wp * rlc_twoChannelForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q =
      wd * FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q :=
    mul_left_cancel₀ hB.ne' hcrossB
  unfold FK.bcProb rlc_twoChannelForcedDualProb
  exact (div_eq_div_iff hZp hZd).2 hcross

end
end StatMech.Universality
