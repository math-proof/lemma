/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Structure.StatisticalMechanics.Code.Universality.HexBridgeRecon


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


attribute [instance] HexHWDataRecon.Dn_fintype

namespace HexHWDataRecon

variable {c υ : ℕ → ℝ} {x : ℝ} {N : ℕ}


theorem partial_bound_recon (H : HexHWDataRecon c υ x N) :
    ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by
  classical
  have hx2nn : (0 : ℝ) ≤ (x ^ 2)⁻¹ := by positivity
  
  have hprodSumm : Summable (fun p : H.S × H.S => H.wtS p.1 * H.wtS p.2) :=
    H.S_summable.mul_of_nonneg H.S_summable H.wtS_nn H.wtS_nn
  have hprodEq : (∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2) = (∑' s, H.wtS s) ^ 2 := by
    rw [sq, ← H.S_summable.tsum_mul_tsum H.S_summable hprodSumm]
  
  have hcap : (∑ d, H.wtγ d) ≤ (x ^ 2)⁻¹ * (∑' s, H.wtS s) ^ 2 := by
    calc (∑ d, H.wtγ d)
        ≤ ∑ d : H.Dn, (x ^ 2)⁻¹ * (H.wtS (H.decomp d).1 * H.wtS (H.decomp d).2) :=
          Finset.sum_le_sum (fun d _ => H.weight_bound d)
      _ = (x ^ 2)⁻¹ * ∑ d : H.Dn, (H.wtS (H.decomp d).1 * H.wtS (H.decomp d).2) := by
          rw [Finset.mul_sum]
      _ = (x ^ 2)⁻¹ * ∑ p ∈ Finset.univ.image H.decomp, H.wtS p.1 * H.wtS p.2 := by
          rw [Finset.sum_image (fun a _ b _ h => H.decomp_inj h)]
      _ ≤ (x ^ 2)⁻¹ * ∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2 := by
          apply mul_le_mul_of_nonneg_left _ hx2nn
          exact Summable.sum_le_tsum _
            (fun p _ => mul_nonneg (H.wtS_nn _) (H.wtS_nn _)) hprodSumm
      _ = (x ^ 2)⁻¹ * (∑' s, H.wtS s) ^ 2 := by rw [hprodEq]
  rw [← H.partial_eq]
  calc (∑ d, H.wtγ d) ≤ (x ^ 2)⁻¹ * (∑' s, H.wtS s) ^ 2 := hcap
    _ = (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by rw [H.half_sum_eq]
    _ ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by
        nlinarith [mul_nonneg hx2nn (sq_nonneg (∏' T, (1 + υ T)))]

end HexHWDataRecon


theorem hexZ_conv_recon (c upsx : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hc : ∀ n, 0 ≤ c n)
    (hbridge : ∀ N, ∑ n ∈ Finset.range N, c n * x ^ n
        ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + upsx T)) ^ 2) :
    Summable (fun n => c n * x ^ n) := by
  refine summable_of_sum_range_le
    (f := fun n => c n * x ^ n) (c := 2 * (x ^ 2)⁻¹ * (∏' T, (1 + upsx T)) ^ 2) ?_ ?_
  · intro n; exact mul_nonneg (hc n) (pow_nonneg (le_of_lt hx) n)
  · intro N; exact hbridge N


theorem hexZ_conv_recon_from_geometry (c : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hlt : x < hexChiE) (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) := by
  set upsx : ℕ → ℝ := fun T => (C T).colSum x with hupsx
  
  
  
  
  have hυnn : ∀ T, 0 ≤ upsx T := fun T => (C T).colSum_nonneg (le_of_lt hx)
  have hυle : ∀ T, upsx T ≤ (x / hexChiE) ^ T :=
    fun T => (C T).colSum_le_pow (le_of_lt hx) hexChiE_pos (le_of_lt hlt)
  have hsum : Summable upsx := hex_ups_summable upsx x (le_of_lt hx) hlt hυnn hυle
  have _hmul : Multipliable (fun T => 1 + upsx T) := hex_bridge_multipliable upsx hsum
  refine hexZ_conv_recon c upsx x hx hc ?_
  intro N
  exact (H N).partial_bound_recon

end StatMech.Universality
