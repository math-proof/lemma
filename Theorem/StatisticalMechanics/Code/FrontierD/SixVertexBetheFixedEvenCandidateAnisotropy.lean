/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedEvenPositiveBetheRootAt_eq
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexFixedEvenPositiveBetheRootAt s k j c =
      sixVertexFixedEvenPositiveBetheRoots hc s k j := by
  unfold sixVertexFixedEvenPositiveBetheRootAt
    sixVertexFixedEvenPositiveBetheIndex
    sixVertexFixedEvenPositiveBetheRoots
    sixVertexFixedEvenChargeBetheRoots
  rw [sixVertexFixedChargeBetheRootAt_eq hc]

theorem tendsto_sixVertexFixedEvenPositiveBetheRootAt
    (s k : Nat) (j : Fin (s + k + 1)) :
    Tendsto (sixVertexFixedEvenPositiveBetheRootAt s k j) atTop
      (nhds (sixVertexFixedEvenPositiveLimitingRoot s k j)) := by
  exact tendsto_sixVertexFixedChargeBetheRootAt (2 * s) k
    (sixVertexFixedEvenPositiveBetheIndex s k j)

theorem sixVertexFixedEvenPositiveLimitingRoot_pos
    (s k : Nat) (j : Fin (s + k + 1)) :
    0 < sixVertexFixedEvenPositiveLimitingRoot s k j := by
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount (2 * s) k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos (2 * s) k
  unfold sixVertexFixedEvenPositiveLimitingRoot
    sixVertexFixedChargeLimitingRoot
  apply div_pos
  · apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
    rw [sixVertexCentralQuantumNumber_eq]
    unfold sixVertexFixedEvenPositiveBetheIndex
    simp only [Fin.val_cast, Fin.natAdd]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    have hj0 : (0 : Real) <= j.val := by positivity
    push_cast
    nlinarith
  · exact hm

theorem sixVertexFixedEvenPositiveLimitingPhase_ne_one
    (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexBethePhase (sixVertexFixedEvenPositiveLimitingRoot s k j) ≠ 1 := by
  intro h
  have hphase0 :
      sixVertexBethePhase (sixVertexFixedEvenPositiveLimitingRoot s k j) =
        sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using h
  have hroot := sixVertexBethePhase_injective_on_Ioo
    (sixVertexFixedChargeLimitingRoot_mem_Ioo (2 * s) k
      (sixVertexFixedEvenPositiveBetheIndex s k j))
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0
  exact (sixVertexFixedEvenPositiveLimitingRoot_pos s k j).ne' hroot

theorem tendsto_sixVertexFixedEvenPairScale :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 <= c := le_trans (le_max_left _ _) hc
    have hcb : b <= c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)

theorem tendsto_sixVertexFixedChargeSquare_div_pairScale :
    Tendsto (fun c : Real => c ^ 2 / (c ^ 2 - 2)) atTop (nhds 1) := by
  have hinv : Tendsto (fun c : Real => 2 / (c ^ 2 - 2))
      atTop (nhds 0) :=
    tendsto_sixVertexFixedEvenPairScale.const_div_atTop 2
  have heq : (fun c : Real => c ^ 2 / (c ^ 2 - 2)) =ᶠ[atTop]
      fun c => 1 + 2 / (c ^ 2 - 2) := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
    field_simp [hd]
    ring
  have hadd : Tendsto (fun c : Real => 1 + 2 / (c ^ 2 - 2))
      atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : Real => (1 : Real))
        atTop (nhds 1)).add hinv)
  exact hadd.congr' heq.symm

theorem tendsto_sixVertexFixedChargePairScale_inv_complex :
    Tendsto (fun c : Real => ((1 / (c ^ 2 - 2) : Real) : Complex))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun c : Real => 1 / (c ^ 2 - 2))
      atTop (nhds 0) :=
    tendsto_sixVertexFixedEvenPairScale.const_div_atTop 1
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal


theorem tendsto_sixVertexFixedChargeBetheM_normalized
    (r k : Nat) (j : Fin (sixVertexFixedChargeBetheParticleCount r k))
    (hphase : sixVertexFixedChargeLimitingPhase r k j ≠ 1) :
    Tendsto
      (fun c => sixVertexBetheM c
          (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) /
        (c ^ 2 - 2 : Real))
      atTop
      (nhds (-1 / (1 - sixVertexFixedChargeLimitingPhase r k j))) := by
  let z : Real -> Complex := fun c =>
    sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)
  let z0 : Complex := sixVertexFixedChargeLimitingPhase r k j
  have hz : Tendsto z atTop (nhds z0) :=
    tendsto_sixVertexFixedChargeBethePhaseAt r k j
  have hden : 1 - z0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hphase)
  have hratioReal := tendsto_sixVertexFixedChargeSquare_div_pairScale
  have hratio : Tendsto
      (fun c : Real => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)))
      atTop (nhds 1) := by
    change Tendsto
      (fun c : Real => Complex.ofReal (c ^ 2 / (c ^ 2 - 2)))
      atTop (nhds (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hratioReal
  have hmain : Tendsto
      (fun c => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (1 / (1 - z0))) :=
    hratio.div (tendsto_const_nhds.sub hz) hden
  have hlimit0 :=
    tendsto_sixVertexFixedChargePairScale_inv_complex.sub hmain
  have hlimit : Tendsto
      (fun c => ((1 / (c ^ 2 - 2) : Real) : Complex) -
        (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (-1 / (1 - z0))) := by
    convert hlimit0 using 1 <;> simp [div_eq_mul_inv]
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hdR : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hdR
  dsimp [z]
  unfold sixVertexBetheM
  push_cast
  field_simp [hd]

theorem tendsto_sixVertexFixedEvenPositiveBetheM_normalized
    (s k : Nat) (j : Fin (s + k + 1)) :
    Tendsto
      (fun c => sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
        (c ^ 2 - 2 : Real))
      atTop
      (nhds (-1 / (1 - sixVertexBethePhase
        (sixVertexFixedEvenPositiveLimitingRoot s k j)))) := by
  let z : Real -> Complex := fun c => sixVertexBethePhase
    (sixVertexFixedEvenPositiveBetheRootAt s k j c)
  let z0 : Complex := sixVertexBethePhase
    (sixVertexFixedEvenPositiveLimitingRoot s k j)
  have hz : Tendsto z atTop (nhds z0) := by
    have hcontinuous : Continuous (fun p : Real => sixVertexBethePhase p) := by
      unfold sixVertexBethePhase
      fun_prop
    exact hcontinuous.continuousAt.tendsto.comp
      (tendsto_sixVertexFixedEvenPositiveBetheRootAt s k j)
  have hden : 1 - z0 ≠ 0 := sub_ne_zero.mpr
    (Ne.symm (sixVertexFixedEvenPositiveLimitingPhase_ne_one s k j))
  have hratioReal := tendsto_sixVertexFixedChargeSquare_div_pairScale
  have hratio : Tendsto
      (fun c : Real => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)))
      atTop (nhds 1) := by
    change Tendsto
      (fun c : Real => Complex.ofReal (c ^ 2 / (c ^ 2 - 2)))
      atTop (nhds (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hratioReal
  have hmain : Tendsto
      (fun c => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (1 / (1 - z0))) :=
    hratio.div (tendsto_const_nhds.sub hz) hden
  have hlimit0 :=
    tendsto_sixVertexFixedChargePairScale_inv_complex.sub hmain
  have hlimit : Tendsto
      (fun c => ((1 / (c ^ 2 - 2) : Real) : Complex) -
        (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (-1 / (1 - z0))) := by
    convert hlimit0 using 1 <;> simp [div_eq_mul_inv]
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hdR : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hdR
  dsimp [z]
  unfold sixVertexBetheM
  push_cast
  field_simp [hd]


end
end StatMech.FrontierD
