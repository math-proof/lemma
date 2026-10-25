/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSelectedInitialLogContribution_bounds
    {c : Real} (hc : 2 < c) (J k : Nat) :
    0 ≤ sixVertexSelectedInitialLogContribution hc J k ∧
      sixVertexSelectedInitialLogContribution hc J k ≤
        (2 * (J : Real) *
          Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) /
            (sixVertexFourWidth 0 k : Real) := by
  let S : Finset (Fin (k + 1)) := Finset.univ.filter (fun j => j.val < J)
  let B : Real := Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hq : 1 < (c ^ 2 - 2) / 2 := by nlinarith
  have htermNonneg (j : Fin (k + 1)) :
      0 ≤ Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
    have hnorm := sixVertexSelectedBetheM_norm_ge hc k j
    have hone : 1 ≤ ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ :=
      hq.le.trans hnorm
    exact Real.log_nonneg hone
  have htermUpper (j : Fin (k + 1)) :
      Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤
        B := by
    have hquant := sixVertexSelectedBetheM_log_norm_le_quantile hc k j
    have hj0 : (0 : Real) ≤ j := by positivity
    have hs : (1 : Real) ≤ 2 * (j : Real) + 1 := by linarith
    have hnum : 0 ≤ c ^ 2 * (sixVertexFourWidth 0 k : Real) := by positivity
    have hfrac : c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1)) ≤
        c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2 := by
      apply div_le_div_of_nonneg_left hnum (by positivity)
      nlinarith
    have hleft : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by positivity
    exact hquant.trans (Real.log_le_log hleft hfrac)
  have hcard : (S.card : Real) ≤ J := by
    have hsub : S ⊆ Finset.univ.filter (fun j : Fin (k + 1) => j.val < J) :=
      fun _ h => h
    have hcardNat : S.card ≤ J := by
      dsimp [S]
      calc
        (Finset.univ.filter (fun j : Fin (k + 1) => j.val < J)).card ≤
            (Finset.range J).card := by
          apply Finset.card_le_card_of_injOn (fun j => j.val)
          · intro j hj
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
          · intro a ha b hb hab
            exact Fin.ext hab
        _ = J := by simp
    exact_mod_cast hcardNat
  have hsumNonneg : 0 ≤ ∑ j ∈ S, Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
    apply Finset.sum_nonneg
    intro j hj
    exact htermNonneg j
  have hsumUpper : (∑ j ∈ S, Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖) ≤
      (J : Real) * B := by
    calc
      _ ≤ ∑ _j ∈ S, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact htermUpper j
      _ = (S.card : Real) * B := by simp
      _ ≤ (J : Real) * B := by
        apply mul_le_mul_of_nonneg_right hcard
        dsimp [B]
        apply Real.log_nonneg
        have hN4 : (4 : Real) ≤ sixVertexFourWidth 0 k := by
          rw [sixVertexFourWidth]
          push_cast
          norm_num
        nlinarith [sq_nonneg c]
  unfold sixVertexSelectedInitialLogContribution
  change 0 ≤ (2 * ∑ j ∈ S, _) / _ ∧
    (2 * ∑ j ∈ S, _) / _ ≤ (2 * (J : Real) * B) / _
  constructor
  · positivity
  · apply div_le_div_of_nonneg_right _ hN.le
    nlinarith


theorem sixVertexSelectedInitialLogContribution_tendsto_zero
    {c : Real} (hc : 2 < c) (J : Nat) :
    Tendsto (sixVertexSelectedInitialLogContribution hc J) atTop (nhds 0) := by
  let A : Real := 2 * c ^ 2
  let m : Nat → Real := fun k => (k + 1 : Nat)
  have hA : 0 < A := by dsimp [A]; positivity
  have hm : Tendsto m atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hconst : Tendsto (fun k => Real.log A / m k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hm
  have hlog : Tendsto (fun k => Real.log (m k) / m k) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hm
    simpa [pow_one] using h
  have hupper : Tendsto (fun k : Nat =>
      (2 * (J : Real) *
        Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) /
          (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
    have hadd := hconst.add hlog
    have hmul := hadd.const_mul ((J : Real) / 2)
    convert hmul using 1
    · funext k
      have hmk : 0 < m k := by dsimp [m]; positivity
      rw [sixVertexFourWidth]
      dsimp [m, A]
      push_cast
      rw [show c ^ 2 * (4 * (0 + (k : Real) + 1)) / 2 =
          (2 * c ^ 2) * ((k : Real) + 1) by ring]
      rw [Real.log_mul (by positivity : (2 * c ^ 2 : Real) ≠ 0)
        (by positivity : ((k : Real) + 1) ≠ 0)]
      field_simp
      ring
    · norm_num
  apply squeeze_zero
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc J k).1
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc J k).2
  · exact hupper


theorem sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule
    {c : Real} (hc : 2 < c) (J : Nat -> Nat)
    (hscale : Tendsto (fun k : Nat =>
      (2 * (J k : Real) *
        Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) /
          (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
    Tendsto (fun k => sixVertexSelectedInitialLogContribution hc (J k) k)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc (J k) k).1
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc (J k) k).2
  · exact hscale


theorem sixVertexSelectedInitialLogContribution_log2_tendsto_zero
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexSelectedInitialLogContribution hc
      (Nat.log2 (k + 1)) k) atTop (nhds 0) := by
  apply sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule hc
  let A : Real := 2 * c ^ 2
  let m : Nat -> Real := fun k => (k + 1 : Nat)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 <= A := by dsimp [A]; nlinarith [sq_nonneg c]
  have hm : Tendsto m atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog1 : Tendsto (fun k => Real.log (m k) / m k) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hm
    simpa [pow_one] using h
  have hlog2 : Tendsto (fun k => Real.log (m k) ^ 2 / m k) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hm
    simpa using h
  have hupper : Tendsto (fun k =>
      (Real.log A / (2 * Real.log 2)) * (Real.log (m k) / m k) +
      (1 / (2 * Real.log 2)) * (Real.log (m k) ^ 2 / m k))
      atTop (nhds 0) := by
    convert (hlog1.const_mul (Real.log A / (2 * Real.log 2))).add
      (hlog2.const_mul (1 / (2 * Real.log 2))) using 1 <;> norm_num
  refine squeeze_zero ?_ ?_ hupper
  · intro k
    have harg : 1 <= c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2 := by
      have hN : (4 : Real) <= sixVertexFourWidth 0 k := by
        rw [sixVertexFourWidth]
        push_cast
        norm_num
      nlinarith [sq_nonneg c]
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg harg)) (by positivity)
  · intro k
    have hmpos : 0 < m k := by dsimp [m]; positivity
    have hmone : 1 <= m k := by
      dsimp [m]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hlogm : 0 <= Real.log (m k) := Real.log_nonneg hmone
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hJ := Real.log2_le_logb (k + 1)
    change (Nat.log2 (k + 1) : Real) <= Real.log (m k) / Real.log 2 at hJ
    have hfactor : 0 <= Real.log A + Real.log (m k) := by
      exact add_nonneg (Real.log_nonneg hAone) hlogm
    have hmul := mul_le_mul_of_nonneg_right hJ hfactor
    rw [sixVertexFourWidth]
    dsimp [m, A] at hmul ⊢
    push_cast at hmul ⊢
    rw [show c ^ 2 * (4 * (0 + (k : Real) + 1)) / 2 =
        (2 * c ^ 2) * ((k : Real) + 1) by ring]
    rw [Real.log_mul (by positivity : (2 * c ^ 2 : Real) ≠ 0)
      (by positivity : ((k : Real) + 1) ≠ 0)]
    field_simp [hlog2pos.ne', hmpos.ne'] at hmul ⊢
    nlinarith


theorem sixVertex_log2Cutoff_tendsto_atTop :
    Tendsto (fun k : Nat => Nat.log2 (k + 1)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 ^ b, ?_⟩
  intro k hk
  rw [Nat.le_log2 (by omega)]
  omega


theorem sixVertex_log2Cutoff_div_width_tendsto_zero :
    Tendsto (fun k : Nat =>
      (Nat.log2 (k + 1) : Real) / (k + 1 : Real)) atTop (nhds 0) := by
  let m : Nat -> Real := fun k => (k + 1 : Nat)
  have hm : Tendsto m atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun k =>
      (1 / Real.log 2) * (Real.log (m k) / m k)) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hm
    have h' : Tendsto (fun k => Real.log (m k) / m k) atTop (nhds 0) := by
      simpa [pow_one] using h
    convert h'.const_mul (1 / Real.log 2) using 1 <;> norm_num
  refine squeeze_zero ?_ ?_ hupper
  · intro k
    positivity
  · intro k
    have hmpos : 0 < m k := by dsimp [m]; positivity
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hJ := Real.log2_le_logb (k + 1)
    change (Nat.log2 (k + 1) : Real) <= Real.log (m k) / Real.log 2 at hJ
    dsimp [m] at hmpos hJ ⊢
    push_cast at hmpos hJ ⊢
    rw [div_le_iff₀ hmpos]
    field_simp [hlog2pos.ne'] at hJ ⊢
    nlinarith

end
end StatMech.FrontierD
