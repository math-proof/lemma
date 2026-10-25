/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_two_le_sixVertexPerronGaugeStage
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop, 2 ≤ sixVertexPerronGaugeStage hc k :=
  (tendsto_sixVertexPerronGaugeStage hc).eventually
    (eventually_ge_atTop 2)

theorem tendsto_sixVertexCanonicalPerronLogEpsilon
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalPerronLogEpsilon hc) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hinv : Tendsto (fun k =>
      (1 : Real) / sixVertexPerronGaugeStage hc k) atTop (nhds 0) :=
    hstageReal.const_div_atTop 1
  apply squeeze_zero' (g := fun k =>
    (1 : Real) / sixVertexPerronGaugeStage hc k)
  · filter_upwards [] with k
    exact div_nonneg zero_le_one
      (pow_nonneg (Nat.cast_nonneg _) 4)
  · filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc]
      with k hk
    let s : Real := sixVertexPerronGaugeStage hc k
    have hs : 1 ≤ s := by
      dsimp [s]
      exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
    have hpow : s ≤ s ^ 4 := by
      simpa using pow_le_pow_right₀ hs (show 1 ≤ 4 by omega)
    exact one_div_le_one_div_of_le (by positivity) hpow
  · exact hinv

theorem eventually_sixVertexCanonicalPerronLogEpsilon_pos
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop, 0 < sixVertexCanonicalPerronLogEpsilon hc k := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc] with k hk
  unfold sixVertexCanonicalPerronLogEpsilon
  positivity

theorem sixVertexCanonicalPerronLogCutoff_pos
    {c : Real} (hc : 2 < c) (k : Nat) :
    0 < sixVertexCanonicalPerronLogCutoff hc k := by
  unfold sixVertexCanonicalPerronLogCutoff
  exact Nat.zero_lt_succ _

theorem eventually_sixVertexCanonicalPerronLogCutoff_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalPerronLogCutoff hc k ≤ k + 1 := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc] with k hk
  unfold sixVertexCanonicalPerronLogCutoff
  have hm : 0 < k + 1 := by omega
  have hlt := Nat.div_lt_self hm (by omega : 1 < sixVertexPerronGaugeStage hc k)
  omega

theorem tendsto_sixVertexCanonicalPerronLogCutoff_div_width
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      (sixVertexCanonicalPerronLogCutoff hc k : Real) /
        (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
  let s : Nat → Real := fun k => sixVertexPerronGaugeStage hc k
  let m : Nat → Real := fun k => k + 1
  have hs : Tendsto s atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hm : Tendsto m atTop atTop :=
    by
      simpa [m, Function.comp_def] using
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsInv : Tendsto (fun k => (1 / 4 : Real) / s k)
      atTop (nhds 0) := hs.const_div_atTop (1 / 4)
  have hmInv : Tendsto (fun k => (1 / 4 : Real) / m k)
      atTop (nhds 0) := hm.const_div_atTop (1 / 4)
  have hupper : Tendsto (fun k =>
      (1 / 4 : Real) / s k + (1 / 4 : Real) / m k)
      atTop (nhds 0) := by simpa using hsInv.add hmInv
  apply squeeze_zero' (g := fun k =>
    (1 / 4 : Real) / s k + (1 / 4 : Real) / m k)
  · filter_upwards [] with k
    positivity
  · filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc]
      with k hk
    have hspos : (0 : Real) < s k := by
      dsimp [s]
      exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
    have hmpos : (0 : Real) < m k := by dsimp [m]; positivity
    have hcast :
        (sixVertexCanonicalPerronLogCutoff hc k : Real) ≤
          m k / s k + 1 := by
      dsimp [m, s]
      unfold sixVertexCanonicalPerronLogCutoff
      push_cast
      exact add_le_add
        (by simpa using
          (Nat.cast_div_le (m := k + 1)
            (n := sixVertexPerronGaugeStage hc k) (α := Real))) le_rfl
    rw [sixVertexFourWidth]
    push_cast
    simp only [zero_add]
    calc
      (sixVertexCanonicalPerronLogCutoff hc k : Real) / (4 * m k) ≤
          (m k / s k + 1) / (4 * m k) :=
        div_le_div_of_nonneg_right hcast (by positivity)
      _ = (1 / 4 : Real) / s k + (1 / 4 : Real) / m k := by
        field_simp [hspos.ne', hmpos.ne']
  · exact hupper

theorem tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronInitialLogContribution hc
        (sixVertexCanonicalPerronLogCutoff hc k) k)
      atTop (nhds 0) := by
  exact
    sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear
      hc
      (sixVertexCanonicalPerronLogCutoff hc)
      (Filter.Eventually.of_forall
        (sixVertexCanonicalPerronLogCutoff_pos hc))
      (eventually_sixVertexCanonicalPerronLogCutoff_le hc)
      (tendsto_sixVertexCanonicalPerronLogCutoff_div_width hc)

theorem tendsto_sixVertexCanonicalPerronRegularizedTailBound
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalPerronLogEpsilon hc k *
          (sixVertexFourWidth 0 k : Real) /
        (4 * (sixVertexCanonicalPerronLogCutoff hc k : Real)))
      atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hinv : Tendsto (fun k =>
      (1 : Real) / sixVertexPerronGaugeStage hc k) atTop (nhds 0) :=
    hstageReal.const_div_atTop 1
  apply squeeze_zero' (g := fun k =>
    (1 : Real) / sixVertexPerronGaugeStage hc k)
  · filter_upwards [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc]
      with k hk
    positivity
  · filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc]
      with k hk
    have hsNat : 0 < sixVertexPerronGaugeStage hc k := by omega
    have hs : (0 : Real) < sixVertexPerronGaugeStage hc k := by
      exact_mod_cast hsNat
    have hJ := sixVertexCanonicalPerronLogCutoff_pos hc k
    have hmulNat : k + 1 ≤ sixVertexPerronGaugeStage hc k *
        sixVertexCanonicalPerronLogCutoff hc k := by
      simpa [sixVertexCanonicalPerronLogCutoff] using
        (Nat.lt_mul_div_succ (k + 1) hsNat).le
    have hmul : ((k + 1 : Nat) : Real) ≤
        (sixVertexPerronGaugeStage hc k : Real) *
          (sixVertexCanonicalPerronLogCutoff hc k : Real) := by
      exact_mod_cast hmulNat
    have hsone : (1 : Real) ≤ sixVertexPerronGaugeStage hc k := by
      exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
    have hpow : (sixVertexPerronGaugeStage hc k : Real) ≤
        (sixVertexPerronGaugeStage hc k : Real) ^ 3 := by
      simpa using pow_le_pow_right₀ hsone (show 1 ≤ 3 by omega)
    have hmul3 : ((k : Real) + 1) ≤
        (sixVertexPerronGaugeStage hc k : Real) ^ 3 *
          (sixVertexCanonicalPerronLogCutoff hc k : Real) := by
      have hJnonneg : (0 : Real) ≤
          sixVertexCanonicalPerronLogCutoff hc k := by positivity
      have hscale := mul_le_mul_of_nonneg_right hpow hJnonneg
      norm_num at hmul ⊢
      exact hmul.trans hscale
    unfold sixVertexCanonicalPerronLogEpsilon
    rw [sixVertexFourWidth]
    push_cast
    simp only [zero_add, Nat.cast_add, Nat.cast_one]
    change ((1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 4) *
        (4 * ((k : Real) + 1)) /
        (4 * (sixVertexCanonicalPerronLogCutoff hc k : Real)) ≤
          1 / (sixVertexPerronGaugeStage hc k : Real)
    field_simp [hs.ne', (show
      (sixVertexCanonicalPerronLogCutoff hc k : Real) ≠ 0 by
        exact_mod_cast hJ.ne')]
    exact hmul3
  · exact hinv


theorem tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c
            (sixVertexCanonicalPerronLogEpsilon hc k)) k)
      atTop (nhds 0) := by
  let margin : Real := (c ^ 2 - 2) ^ 2 - 4
  have hmargin : 0 < margin := by
    dsimp [margin]
    have hc2 : 2 < c ^ 2 - 2 := by nlinarith [sq_nonneg (c - 2)]
    nlinarith
  have hepsUpper : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalPerronLogEpsilon hc k ≤ margin :=
    (tendsto_sixVertexCanonicalPerronLogEpsilon hc).eventually
      (Iic_mem_nhds hmargin)
  have hupper :=
    (tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule hc).add
      (tendsto_sixVertexCanonicalPerronRegularizedTailBound hc)
  apply squeeze_zero'
  · filter_upwards
      [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc, hepsUpper]
      with k heps hepsLe
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc heps hepsLe
      (sixVertexCanonicalPerronLogCutoff_pos hc k) k).1
  · filter_upwards
      [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc, hepsUpper]
      with k heps hepsLe
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc heps hepsLe
      (sixVertexCanonicalPerronLogCutoff_pos hc k) k).2
  · simpa using hupper

end
end StatMech.FrontierD
