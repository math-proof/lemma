/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedChargeBetheRootError
    (r k : Nat) (j l : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (sixVertexFixedChargeBetheRootError r k j l) atTop (nhds 0) := by
  exact tendsto_sixVertexTheta_sub_linear_atTop
    (sixVertexFixedChargeBetheRootAt r k j)
    (sixVertexFixedChargeBetheRootAt r k l)

theorem tendsto_sixVertexFixedChargeBetheRootError_sum
    (r k : Nat) (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (fun c => ∑ l, sixVertexFixedChargeBetheRootError r k j l c)
      atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ
    (fun l _ => tendsto_sixVertexFixedChargeBetheRootError r k j l)

theorem sixVertexFixedChargeBetheRootAt_eq_quantum_sub_error
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeBetheRootAt r k j c =
      (2 * Real.pi * sixVertexCentralQuantumNumber j -
          ∑ l, sixVertexFixedChargeBetheRootError r k j l c) /
        (sixVertexFixedChargeBetheComplementCount r k : Real) := by
  have heq := sixVertexFixedChargeBetheRootAt_equation hc r k j
  have hsum := sixVertexFixedChargeBetheRootAt_sum_eq_zero hc r k
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount r k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have herr :
      (∑ l, sixVertexFixedChargeBetheRootError r k j l c) =
        (∑ l, sixVertexTheta c
          (sixVertexFixedChargeBetheRootAt r k j c)
          (sixVertexFixedChargeBetheRootAt r k l c)) +
        (sixVertexFixedChargeBetheParticleCount r k : Real) *
          sixVertexFixedChargeBetheRootAt r k j c := by
    unfold sixVertexFixedChargeBetheRootError
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hwidth :
      (sixVertexFourWidth r k : Real) =
        (sixVertexFixedChargeBetheComplementCount r k : Real) +
          (sixVertexFixedChargeBetheParticleCount r k : Real) := by
    rw [sixVertexFixedChargeBetheComplementCount_eq,
      sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    ring
  rw [herr, eq_div_iff hm.ne']
  rw [hwidth] at heq
  linarith [heq]


theorem tendsto_sixVertexFixedChargeBetheRootAt (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (sixVertexFixedChargeBetheRootAt r k j) atTop
      (nhds (sixVertexFixedChargeLimitingRoot r k j)) := by
  have herror := tendsto_sixVertexFixedChargeBetheRootError_sum r k j
  have hformula : (fun c => sixVertexFixedChargeBetheRootAt r k j c) =ᶠ[atTop]
      fun c =>
        (2 * Real.pi * sixVertexCentralQuantumNumber j -
            ∑ l, sixVertexFixedChargeBetheRootError r k j l c) /
          (sixVertexFixedChargeBetheComplementCount r k : Real) := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    exact sixVertexFixedChargeBetheRootAt_eq_quantum_sub_error hc r k j
  apply Tendsto.congr' hformula.symm
  simpa [sixVertexFixedChargeLimitingRoot] using
    (tendsto_const_nhds.sub herror).div_const
      (sixVertexFixedChargeBetheComplementCount r k : Real)


theorem tendsto_sixVertexFixedChargeBethePhaseAt (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto
      (fun c => sixVertexBethePhase
        (sixVertexFixedChargeBetheRootAt r k j c)) atTop
      (nhds (sixVertexFixedChargeLimitingPhase r k j)) := by
  have hcontinuous : Continuous (fun p : Real => sixVertexBethePhase p) := by
    unfold sixVertexBethePhase
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp
    (tendsto_sixVertexFixedChargeBetheRootAt r k j)

end
end StatMech.FrontierD
