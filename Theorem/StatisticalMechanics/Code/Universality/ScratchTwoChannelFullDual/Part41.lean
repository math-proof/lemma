/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part49
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) :
    rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma' A) =
      rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q A := by
  classical
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let summand : ConfigSpace (Sym2 (RlcConnectorVertex n)) → Real :=
    fun rho =>
      (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma' A).indicator
          (fun _ => (1 : Real)) rho *
        rlc_twoChannelForcedDualProb gamma gamma' p q rho
  have hreindex := Equiv.sum_comp split
    (fun pair : RlcTwoChannelEdgeConfig gamma gamma' ×
        RlcTwoChannelOffGraphConfig gamma gamma' =>
      summand (split.symm pair))
  unfold rlc_twoChannelForcedDualEventMass
    rlc_twoChannelFaithfulForcedDualEdgeEventMass
  change (∑ rho, summand rho) = _
  calc
    (∑ rho, summand rho) = ∑ pair, summand (split.symm pair) := by
      simpa only [Equiv.symm_apply_apply] using hreindex
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ outside : RlcTwoChannelOffGraphConfig gamma gamma',
          A.indicator (fun _ => (1 : Real))
              (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
            rlc_twoChannelForcedDualProb gamma gamma' p q
              (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro outside _
      change (if rlc_twoChannelFaithfulDualConfig gamma gamma'
          (split (split.symm (omega, outside))).1 ∈ A then 1 else 0) *
          rlc_twoChannelForcedDualProb gamma gamma' p q
            (split.symm (omega, outside)) =
        (if rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈ A
          then 1 else 0) *
          rlc_twoChannelForcedDualProb gamma gamma' p q
            (split.symm (omega, outside))
      rw [split.apply_symm_apply]
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ _outside : RlcTwoChannelOffGraphConfig gamma gamma',
          A.indicator (fun _ => (1 : Real))
              (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
            rlc_twoChannelForcedDualProb gamma gamma' p q
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro outside _
      rw [rlc_twoChannelForcedDualProb_edgeConfigCombine]
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        A.indicator (fun _ => (1 : Real))
            (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
          (Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
            rlc_twoChannelForcedDualProb gamma gamma' p q
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)) := by
      apply Finset.sum_congr rfl
      intro omega _
      simp [nsmul_eq_mul]
      ring
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        A.indicator (fun _ => (1 : Real))
            (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
          rlc_twoChannelFaithfulForcedDualEdgeProb
            gamma gamma' p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb
        gamma gamma' hp hp1 hq]

end
end StatMech.Universality
