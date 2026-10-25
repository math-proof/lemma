/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    0 ≤ Real.log ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ := by
  apply Real.log_nonneg
  have hq : 1 < (c ^ 2 - 2) / 2 := by nlinarith
  exact hq.le.trans
    (sixVertexCanonicalDensityPerronBetheM_norm_ge hc k j)

theorem sixVertexCanonicalDensityPerronInitialLogContribution_nonneg
    {c : Real} (hc : 2 < c) (J k : Nat) :
    0 ≤ sixVertexCanonicalDensityPerronInitialLogContribution hc J k := by
  unfold sixVertexCanonicalDensityPerronInitialLogContribution
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    exact sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg hc k j
  · positivity


theorem sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial
    {c : Real} (hc : 2 < c) {J k : Nat} (hJ : J ≤ k + 1) :
    sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
      (2 * ((J : Real) *
          Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) -
        Real.log (J.factorial : Real))) /
        (sixVertexFourWidth 0 k : Real) := by
  let S : Finset (Fin (k + 1)) :=
    Finset.univ.filter (fun j => j.val < J)
  let B : Real :=
    Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)
  let f : Fin (k + 1) → Real := fun j =>
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hterm (j : Fin (k + 1)) :
      f j ≤ B - Real.log ((j.val + 1 : Nat) : Real) := by
    have hquant :=
      sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile hc k j
    have hnum : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) := by
      positivity
    have hjpos : (0 : Real) < (j.val + 1 : Nat) := by positivity
    have hsmall : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by positivity
    have hfrac : c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1)) ≤
        c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * ((j.val + 1 : Nat) : Real)) := by
      apply div_le_div_of_nonneg_left hnum.le (by positivity)
      push_cast
      nlinarith [show (0 : Real) ≤ j by positivity]
    calc
      f j ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1))) := hquant
      _ ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * ((j.val + 1 : Nat) : Real))) :=
        Real.log_le_log hsmall hfrac
      _ = B - Real.log ((j.val + 1 : Nat) : Real) := by
        dsimp [B]
        rw [show c ^ 2 * (sixVertexFourWidth 0 k : Real) /
            (2 * ((j.val + 1 : Nat) : Real)) =
          (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) /
            ((j.val + 1 : Nat) : Real) by ring]
        rw [Real.log_div (by positivity) hjpos.ne']
  have hsum : (∑ j ∈ S, f j) ≤
      ∑ j ∈ S, (B - Real.log ((j.val + 1 : Nat) : Real)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hterm j
  have hindex :
      (∑ j ∈ S, (B - Real.log ((j.val + 1 : Nat) : Real))) =
        ∑ i ∈ Finset.range J,
          (B - Real.log ((i + 1 : Nat) : Real)) := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro a ha b hb hab
      exact Fin.ext hab
    · intro i hi
      have hiJ := Finset.mem_range.mp hi
      let j : Fin (k + 1) := ⟨i, lt_of_lt_of_le hiJ hJ⟩
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiJ⟩
    · intro j hj
      rfl
  have hlogs :
      (∑ i ∈ Finset.range J, Real.log ((i + 1 : Nat) : Real)) =
        Real.log (J.factorial : Real) := by
    rw [← Real.log_prod (fun i hi => by positivity)]
    apply congrArg Real.log
    norm_cast
    exact Finset.prod_range_add_one_eq_factorial J
  have hsum' : (∑ j ∈ S, f j) ≤
      (J : Real) * B - Real.log (J.factorial : Real) := by
    rw [hindex, Finset.sum_sub_distrib, hlogs] at hsum
    simpa using hsum
  unfold sixVertexCanonicalDensityPerronInitialLogContribution
  change (2 * ∑ j ∈ S, f j) / _ ≤ _
  apply div_le_div_of_nonneg_right _ hN.le
  nlinarith

theorem sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling
    {c : Real} (hc : 2 < c) {J k : Nat} (hJ0 : 0 < J)
    (hJ : J ≤ k + 1) :
    sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
      (2 * (J : Real) *
        (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (J : Real))) + 1)) /
        (sixVertexFourWidth 0 k : Real) := by
  let N : Real := sixVertexFourWidth 0 k
  let B : Real := Real.log (c ^ 2 * N / 2)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hJreal : (0 : Real) < J := by exact_mod_cast hJ0
  have hlogJ : 0 ≤ Real.log (J : Real) :=
    Real.log_nonneg (by exact_mod_cast hJ0)
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hfactorial := Stirling.le_log_factorial_stirling hJ0.ne'
  have hfactorial' :
      (J : Real) * Real.log (J : Real) - (J : Real) ≤
        Real.log (J.factorial : Real) := by
    calc
      (J : Real) * Real.log (J : Real) - (J : Real) ≤
          (J : Real) * Real.log (J : Real) - (J : Real) +
            Real.log (J : Real) / 2 + Real.log (2 * Real.pi) / 2 := by
        nlinarith [hlogJ, hlogTwoPi]
      _ ≤ Real.log (J.factorial : Real) := hfactorial
  have hlog :
      Real.log (c ^ 2 * N / (2 * (J : Real))) =
        B - Real.log (J : Real) := by
    dsimp [B]
    rw [show c ^ 2 * N / (2 * (J : Real)) =
      (c ^ 2 * N / 2) / (J : Real) by ring]
    rw [Real.log_div (by positivity) hJreal.ne']
  have hbase :=
    sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial hc hJ
  change sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
    (2 * ((J : Real) * B - Real.log (J.factorial : Real))) / N at hbase
  change sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
    (2 * (J : Real) *
      (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N
  calc
    sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
        (2 * ((J : Real) * B - Real.log (J.factorial : Real))) / N := hbase
    _ ≤ (2 * (J : Real) *
        (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      rw [hlog]
      nlinarith


theorem sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear
    {c : Real} (hc : 2 < c) (J : Nat → Nat)
    (hJ0 : ∀ᶠ k in atTop, 0 < J k)
    (hJle : ∀ᶠ k in atTop, J k ≤ k + 1)
    (hsublinear : Tendsto (fun k : Nat =>
      (J k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronInitialLogContribution hc (J k) k)
      atTop (nhds 0) := by
  let x : Nat → Real := fun k =>
    (J k : Real) / (sixVertexFourWidth 0 k : Real)
  let C : Real := Real.log (c ^ 2 / 2)
  have hx : Tendsto x atTop (nhds 0) := hsublinear
  have hxlog : Tendsto (fun k => x k * Real.log (x k))
      atTop (nhds 0) := by
    have h := Real.continuous_mul_log.continuousAt.tendsto.comp hx
    simpa using h
  have hupper : Tendsto (fun k =>
      2 * x k * (C - Real.log (x k) + 1)) atTop (nhds 0) := by
    have hlinear := hx.const_mul (2 * (C + 1))
    have hlogterm := hxlog.const_mul 2
    convert hlinear.sub hlogterm using 1
    · funext k
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards [] with k
    exact sixVertexCanonicalDensityPerronInitialLogContribution_nonneg hc
      (J k) k
  · filter_upwards [hJ0, hJle] with k hk0 hkle
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    have hJreal : (0 : Real) < J k := by exact_mod_cast hk0
    have hxpos : 0 < x k := div_pos hJreal hN
    have hratio :
        c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (J k : Real)) =
          (c ^ 2 / 2) / x k := by
      dsimp [x]
      field_simp [hN.ne', hJreal.ne']
    calc
      sixVertexCanonicalDensityPerronInitialLogContribution hc (J k) k ≤
          (2 * (J k : Real) *
            (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
              (2 * (J k : Real))) + 1)) /
            (sixVertexFourWidth 0 k : Real) :=
        sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling
          hc hk0 hkle
      _ = 2 * x k * (C - Real.log (x k) + 1) := by
        rw [hratio, Real.log_div (by positivity : c ^ 2 / 2 ≠ 0)
          hxpos.ne']
        dsimp [x, C]
        ring
  · exact hupper


theorem sixVertexCanonicalDensityPerronInitialLogContribution_log2_tendsto_zero
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronInitialLogContribution hc
        (Nat.log2 (k + 1)) k) atTop (nhds 0) := by
  apply
    sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear
      hc
  · filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Nat.lt_iff_add_one_le, Nat.le_log2 (by omega)]
    omega
  · filter_upwards [] with k
    exact Nat.log2_le_self (k + 1)
  · have h := sixVertex_log2Cutoff_div_width_tendsto_zero.const_mul
        (1 / 4 : Real)
    convert h using 1
    · funext k
      unfold sixVertexFourWidth
      push_cast
      have hkpos : (0 : Real) < (k : Real) + 1 := by positivity
      field_simp [hkpos.ne']
      ring
    · norm_num

end
end StatMech.FrontierD
