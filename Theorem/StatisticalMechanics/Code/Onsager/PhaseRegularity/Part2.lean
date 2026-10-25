/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part2


namespace StatMech.Onsager

theorem ons_one_sub_cos_pos {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonPi : epsilon ≤ Real.pi) :
    0 < 1 - Real.cos epsilon := by
  have h := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show epsilon ∈ Set.Icc 0 Real.pi by exact ⟨hepsilon.le, hepsilonPi⟩)
    hepsilon
  simpa using h

theorem ons_criticalKernelClamp_continuous (epsilon : ℝ)
    (hcut : 0 < 1 - Real.cos epsilon) :
    Continuous (Function.uncurry (ons_criticalKernelClamp epsilon)) := by
  have hden : Continuous
      (fun p : ℝ × ℝ => 2 - Real.cos p.1 - Real.cos p.2) :=
    (continuous_const.sub (Real.continuous_cos.comp continuous_fst)).sub
      (Real.continuous_cos.comp continuous_snd)
  have hmax : Continuous
      (fun p : ℝ × ℝ =>
        max (2 - Real.cos p.1 - Real.cos p.2) (1 - Real.cos epsilon)) :=
    hden.max continuous_const
  apply Continuous.div continuous_const hmax
  intro p
  exact ne_of_gt (hcut.trans_le (le_max_right _ _))

theorem ons_criticalKernelClamp_eq {epsilon delta x y : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdeltaPi : delta ≤ Real.pi)
    (hx : x ∈ Set.Icc epsilon delta) :
    ons_criticalKernelClamp epsilon x y =
      1 / (2 - Real.cos x - Real.cos y) := by
  have hepsilonPi : epsilon ≤ Real.pi := hx.1.trans (hx.2.trans hdeltaPi)
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  have hcos : Real.cos x ≤ Real.cos epsilon :=
    Real.antitoneOn_cos ⟨hepsilon, hepsilonPi⟩ ⟨hepsilon.trans hx.1, hxPi⟩ hx.1
  have hcosy := Real.cos_le_one y
  have hle : 1 - Real.cos epsilon ≤ 2 - Real.cos x - Real.cos y := by
    linarith
  rw [ons_criticalKernelClamp, max_eq_left hle]


theorem ons_wedgeIntegral_continuous {F : ℝ → ℝ → ℝ}
    (hjoint : Continuous (Function.uncurry F)) :
    Continuous (fun x : ℝ => ∫ y in x..(2 * x), F x y) := by
  have hupper : Continuous (fun x : ℝ => 2 * x) :=
    continuous_const.mul continuous_id
  have htoUpper : Continuous (fun x : ℝ =>
      ∫ y in 0..(2 * x), F x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hjoint hupper
  have htoLower : Continuous (fun x : ℝ =>
      ∫ y in 0..x, F x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hjoint continuous_id
  have heq : (fun x : ℝ => ∫ y in x..(2 * x), F x y) =
      (fun x : ℝ =>
        (∫ y in 0..(2 * x), F x y) - ∫ y in 0..x, F x y) := by
    funext x
    symm
    apply intervalIntegral.integral_interval_sub_left
    · exact (hjoint.uncurry_left x).continuousOn.intervalIntegrable
    · exact (hjoint.uncurry_left x).continuousOn.intervalIntegrable
  rw [heq]
  exact htoUpper.sub htoLower

theorem ons_criticalKernelClamp_inner_continuous (epsilon : ℝ)
    (hcut : 0 < 1 - Real.cos epsilon) :
    Continuous (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_criticalKernelClamp epsilon x y) :=
  ons_wedgeIntegral_continuous (ons_criticalKernelClamp_continuous epsilon hcut)

theorem ons_criticalKernel_inner_continuousOn {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y))
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  apply (ons_criticalKernelClamp_inner_continuous epsilon hcut).continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  exact (ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx).symm


theorem ons_criticalKernel_wedgeIntegral_lower {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (h2deltaPi : 2 * delta ≤ Real.pi) :
    (2 / 5 : ℝ) * Real.log (delta / epsilon) ≤
      ∫ x in epsilon..delta,
        ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y) := by
  have hdeltaPi : delta ≤ Real.pi := by linarith
  have hinnerInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y))
      MeasureTheory.volume epsilon delta := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hed] using
      ons_criticalKernel_inner_continuousOn hepsilon hed hdeltaPi
  have hcompCont : ContinuousOn (fun x : ℝ => 2 / (5 * x))
      (Set.uIcc epsilon delta) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.mul continuousOn_id)
    intro x hx
    rw [Set.mem_uIcc] at hx
    intro hzero
    change 5 * x = 0 at hzero
    rcases hx with hx | hx <;> nlinarith
  have hcompInt : IntervalIntegrable (fun x : ℝ => 2 / (5 * x))
      MeasureTheory.volume epsilon delta :=
    hcompCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hed hcompInt hinnerInt
    (fun x hx => ons_criticalKernel_innerIntegral_lower
      (hepsilon.trans_le hx.1) (by nlinarith [hx.2]))
  rw [ons_logKernel_integral hepsilon hed] at hmono
  exact hmono


theorem ons_criticalKernel_wedgeCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..1,
          ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y))
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun n => ?_)
    (ons_logKernel_cutoff_tendsto 1 zero_lt_one)
  apply ons_criticalKernel_wedgeIntegral_lower (Real.exp_pos _)
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  · linarith [Real.pi_gt_three]


theorem ons_criticalSecondKernel_lower_on_wedge {x y : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) (hxy : x ≤ y) (hy2x : y ≤ 2 * x) :
    -4 + 32 / (5 * x ^ 2) ≤
      ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hxpi : x ≤ Real.pi := by linarith
  have hden : 2 - Real.cos x - Real.cos y ≠ 0 :=
    (ons_criticalDenom_pos hx hxpi).ne'
  rw [ons_logGIntBetaDeriv2_betaC x y hden]
  have hkernel := ons_criticalKernel_lower_on_wedge hx h2xpi hxy hy2x
  have hscaled := mul_le_mul_of_nonneg_left hkernel (by norm_num : (0 : ℝ) ≤ 16)
  calc
    -4 + 32 / (5 * x ^ 2) = -4 + 16 * (2 / (5 * x ^ 2)) := by ring
    _ ≤ -4 + 16 * (1 / (2 - Real.cos x - Real.cos y)) :=
      by simpa [add_comm] using add_le_add_left hscaled (-4)
    _ = -4 + 16 / (2 - Real.cos x - Real.cos y) := by ring

theorem ons_criticalSecondKernel_innerIntegral_lower {x : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) :
    -4 * x + 32 / (5 * x) ≤
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hx2x : x ≤ 2 * x := by linarith
  have hxpi : x ≤ Real.pi := by linarith
  have hdenCont : Continuous (fun y : ℝ => 2 - Real.cos x - Real.cos y) :=
    (show Continuous (fun y : ℝ => (2 - Real.cos x) - Real.cos y) from
      continuous_const.sub Real.continuous_cos)
  have hkernelCont : ContinuousOn
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y)) (Set.uIcc x (2 * x)) := by
    apply ContinuousOn.div continuousOn_const hdenCont.continuousOn
    intro y _hy
    exact (ons_criticalDenom_pos hx hxpi).ne'
  have hsecondCont : ContinuousOn
      (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y) (Set.uIcc x (2 * x)) := by
    have hexpr : ContinuousOn
        (fun y : ℝ => -4 + 16 * (1 / (2 - Real.cos x - Real.cos y)))
        (Set.uIcc x (2 * x)) :=
      continuousOn_const.add (continuousOn_const.mul hkernelCont)
    apply hexpr.congr
    intro y _hy
    change ons_logGIntBetaDeriv2 ons_betaC x y =
      -4 + 16 * (1 / (2 - Real.cos x - Real.cos y))
    rw [ons_logGIntBetaDeriv2_betaC x y
      (ons_criticalDenom_pos hx hxpi).ne']
    ring
  have hcompInt : IntervalIntegrable (fun _y : ℝ => -4 + 32 / (5 * x ^ 2))
      MeasureTheory.volume x (2 * x) :=
    continuousOn_const.intervalIntegrable
  have hsecondInt : IntervalIntegrable
      (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume x (2 * x) :=
    hsecondCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx2x hcompInt hsecondInt
    (fun y hy => ons_criticalSecondKernel_lower_on_wedge hx h2xpi hy.1 hy.2)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  convert hmono using 1
  field_simp
  ring

end StatMech.Onsager
