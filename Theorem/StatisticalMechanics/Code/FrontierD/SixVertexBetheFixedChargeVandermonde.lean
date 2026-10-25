/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedChargePairScale :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hc
    have hcb : b ≤ c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)

theorem tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt
    (r k : Nat)
    (i j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto
      (fun c => sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c))
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)))
      atTop (nhds (sixVertexFixedChargeLimitingPhase r k i)) := by
  let u : Real → Complex := fun c =>
    sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c)
  let v : Real → Complex := fun c =>
    sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)
  let u0 := sixVertexFixedChargeLimitingPhase r k i
  let v0 := sixVertexFixedChargeLimitingPhase r k j
  have hu : Tendsto u atTop (nhds u0) :=
    tendsto_sixVertexFixedChargeBethePhaseAt r k i
  have hv : Tendsto v atTop (nhds v0) :=
    tendsto_sixVertexFixedChargeBethePhaseAt r k j
  have hinvR : Tendsto (fun c : Real => 1 / (c ^ 2 - 2))
      atTop (nhds 0) := tendsto_sixVertexFixedChargePairScale.const_div_atTop 1
  have hinvC : Tendsto
      (fun c : Real => Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hlimit : Tendsto
      (fun c => u c + (1 + u c * v c) *
        Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds u0) := by
    simpa using hu.add ((tendsto_const_nhds.add (hu.mul hv)).mul hinvC)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hdC : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hd
  have hinv : Complex.ofReal (1 / (c ^ 2 - 2)) *
      ((c ^ 2 - 2 : Real) : Complex) = 1 := by
    rw [← Complex.ofReal_mul]
    field_simp [hd]
    norm_num
  dsimp [u, v]
  unfold sixVertexNormalizedBethePairFactor
  rw [eq_div_iff hdC]
  symm
  calc
    sixVertexBethePairFactor c
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c))
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) =
      1 + sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) *
          sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c) +
        ((c ^ 2 - 2 : Real) : Complex) *
          sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) := by
        unfold sixVertexBethePairFactor sixVertexDelta
        push_cast
        ring
    _ = (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) +
          (1 + sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) *
            sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) *
              Complex.ofReal (1 / (c ^ 2 - 2))) *
        ((c ^ 2 - 2 : Real) : Complex) := by
      rw [add_mul, mul_assoc, hinv, mul_one]
      ring

end
end StatMech.FrontierD
