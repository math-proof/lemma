/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part48
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp1 : p < 1) (q : Real)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) :
    rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q A =
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
        p q A := by
  unfold rlc_twoChannelFaithfulForcedDualEdgeEventMass
    FK.indexedBcEventMass
  simp_rw [rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed
    gamma gamma' hp1 q]
  exact Equiv.sum_comp (rlc_twoChannelFaithfulDualEquiv gamma gamma')
    (fun eta => A.indicator (fun _ => (1 : Real)) eta *
      FK.indexedBcProb (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q eta)


theorem rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    BeffaraDC.pfdDualWeight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside))) =
      BeffaraDC.pfdDualWeight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
  congr 1
  rw [rlc_openSub_twoChannelAugmented_forceTrace,
    rlc_openSub_twoChannelAugmented_forceTrace,
    rlc_openSub_twoChannel_edgeConfigCombine]


theorem rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_twoChannelForcedDualZ gamma gamma' p q =
      Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
        rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let w : ConfigSpace (Sym2 (RlcConnectorVertex n)) → Real := fun rho =>
    BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho))
  have hreindex := Equiv.sum_comp split
    (fun pair : RlcTwoChannelEdgeConfig gamma gamma' ×
        RlcTwoChannelOffGraphConfig gamma gamma' => w (split.symm pair))
  unfold rlc_twoChannelForcedDualZ
  dsimp only
  change (∑ rho, w rho) = _
  calc
    (∑ rho, w rho) = ∑ pair, w (split.symm pair) := by
      simpa only [Equiv.symm_apply_apply] using hreindex
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ outside : RlcTwoChannelOffGraphConfig gamma gamma',
          w (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ _outside : RlcTwoChannelOffGraphConfig gamma gamma',
          BeffaraDC.pfdDualWeight P p q
            (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma'
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro outside _
      exact rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine
        gamma gamma' p q omega outside
    _ = Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
        rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
      unfold rlc_twoChannelFaithfulForcedDualEdgeZ
      simp [P, nsmul_eq_mul, Finset.mul_sum]

theorem rlc_twoChannelFaithfulForcedDualEdgeZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
  rw [rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed]
  exact mul_pos (pow_pos (by linarith) _)
    (FK.indexedBcZ_pos (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
      hp hp1 hq)


theorem rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
        rlc_twoChannelForcedDualProb gamma gamma' p q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) =
      rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega := by
  have hcard : (Fintype.card
      (RlcTwoChannelOffGraphConfig gamma gamma') : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hZ : rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q ≠ 0 :=
    (rlc_twoChannelFaithfulForcedDualEdgeZ_pos
      gamma gamma' hp hp1 hq).ne'
  unfold rlc_twoChannelForcedDualProb
    rlc_twoChannelFaithfulForcedDualEdgeProb
  dsimp only
  rw [rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ]
  field_simp


end
end StatMech.Universality
