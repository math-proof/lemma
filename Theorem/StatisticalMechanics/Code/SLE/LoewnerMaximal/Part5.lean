/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part4
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem LoewnerForwardSolution.append_terminal
    {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (g : LoewnerForwardSolution W z S)
    (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (g.append h hS hT).curve (S + T) = h.curve T := by
  rcases hT.eq_or_lt with hT0 | hT0
  · subst T
    simp [LoewnerForwardSolution.append, LoewnerForwardSolution.appendCurve,
      h.initial]
  · have hnot : ¬ S + T ≤ S := by linarith
    simp [LoewnerForwardSolution.append, LoewnerForwardSolution.appendCurve,
      hnot]


theorem exists_loewnerBackwardSolution_steps
    {W : ℝ → ℝ} (hW : Continuous W) {u : ℝ} (hu : 0 ≤ u)
    (n : ℕ) {y : ℂ} (hy : 0 < y.im) (hshort : u < y.im ^ 2 / 16) :
    ∃ x : ℂ, ∃ g : LoewnerForwardSolution W x ((n : ℝ) * u),
      g.curve ((n : ℝ) * u) = y := by
  induction n generalizing y with
  | zero =>
      simp only [Nat.cast_zero, zero_mul]
      let g : LoewnerForwardSolution W y (((0 : ℕ) : ℝ) * u) :=
        { curve := fun _ ↦ y
          initial := rfl
          deriv := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr ⊢
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            rw [show Icc (0 : ℝ) 0 = {0} by simp]
            exact HasFDerivWithinAt.singleton
          upper := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            exact mem_upperHalfPlane.mpr hy }
      exact ⟨y, g, rfl⟩
  | succ n ih =>
      obtain ⟨xmid, hlast, hlastEnd⟩ :=
        exists_loewnerBackwardSegment hW (s := (n : ℝ) * u) hu hy hshort
      have hxmid : 0 < xmid.im := by
        rw [← hlast.initial]
        exact mem_upperHalfPlane.mp (hlast.upper 0 ⟨le_rfl, hu⟩)
      have him : y.im ≤ xmid.im := by
        have hant := hlast.im_antitoneOn
          (show (0 : ℝ) ∈ Icc 0 u from ⟨le_rfl, hu⟩)
          (show u ∈ Icc 0 u from ⟨hu, le_rfl⟩) hu
        change (hlast.curve u).im ≤ (hlast.curve 0).im at hant
        rw [hlast.initial, hlastEnd] at hant
        exact hant
      have hshortMid : u < xmid.im ^ 2 / 16 := by
        calc
          u < y.im ^ 2 / 16 := hshort
          _ ≤ xmid.im ^ 2 / 16 := by gcongr
      obtain ⟨x, gprefix, hprefixEnd⟩ := ih hxmid hshortMid
      let hlast' : LoewnerForwardSolution
          (fun r ↦ W ((n : ℝ) * u + r))
          (gprefix.curve ((n : ℝ) * u)) u :=
        { curve := hlast.curve
          initial := hlast.initial.trans hprefixEnd.symm
          deriv := hlast.deriv
          upper := hlast.upper }
      have hlast'End : hlast'.curve u = y := by
        simpa [hlast'] using hlastEnd
      let g := gprefix.append hlast'
        (mul_nonneg (Nat.cast_nonneg n) hu) hu
      have gEnd : g.curve ((n : ℝ) * u + u) = y :=
        (gprefix.append_terminal hlast'
          (mul_nonneg (Nat.cast_nonneg n) hu) hu).trans hlast'End
      rw [show (((n + 1 : ℕ) : ℝ) * u) = (n : ℝ) * u + u by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]]
      exact ⟨x, g, gEnd⟩


theorem exists_loewnerBackwardSolution
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : 0 < y.im) :
    ∃ x : ℂ, ∃ g : LoewnerForwardSolution W x t, g.curve t = y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / y.im ^ 2)
  have hquot : 0 ≤ 16 * t / y.im ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hshort : u < y.im ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * y.im ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hy)).mp hn
    nlinarith
  obtain ⟨x, g, hg⟩ :=
    exists_loewnerBackwardSolution_steps hW hu n hy hshort
  rw [← hnu]
  exact ⟨x, g, hg⟩


theorem exists_loewnerForwardSolution_steps_of_driverBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {T M d u : ℝ}
    (hd : 0 < d) (hu : 0 ≤ u)
    {z : ℂ} (hzim : 0 < z.im) (hzre : M + d ≤ z.re)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
    (hstep : u <
      (z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)) ^ 2 / 8)
    (n : ℕ) (hnT : (n : ℝ) * u ≤ T) :
    Nonempty (LoewnerForwardSolution W z ((n : ℝ) * u)) := by
  induction n with
  | zero =>
      let g : LoewnerForwardSolution W z (((0 : ℕ) : ℝ) * u) :=
        { curve := fun _ ↦ z
          initial := rfl
          deriv := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr ⊢
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            rw [show Icc (0 : ℝ) 0 = {0} by simp]
            exact HasFDerivWithinAt.singleton
          upper := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            exact mem_upperHalfPlane.mpr hzim }
      exact ⟨g⟩
  | succ n ih =>
      let s : ℝ := (n : ℝ) * u
      have hs0 : 0 ≤ s := mul_nonneg (Nat.cast_nonneg n) hu
      have hsT : s ≤ T := by
        dsimp [s]
        calc
          (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
            gcongr
            exact_mod_cast Nat.le_succ n
          _ ≤ T := hnT
      obtain ⟨g⟩ := ih hsT
      let y : ℂ := g.curve s
      have hyUpper : y ∈ upperHalfPlane := g.upper s ⟨hs0, le_rfl⟩
      have hypos : 0 < y.im := mem_upperHalfPlane.mp hyUpper
      have hWprefix : ∀ r ∈ Icc (0 : ℝ) s, W r ≤ M := by
        intro r hr
        exact hW r ⟨hr.1, hr.2.trans hsT⟩
      have himRaw := g.im_ge_exp_of_driverBarrier hd hWprefix hzre s
        (show s ∈ Icc (0 : ℝ) s from ⟨hs0, le_rfl⟩)
      have hcoef : 0 < 2 / (d / 2) ^ 2 := by positivity
      have hexp : Real.exp (-(2 / (d / 2) ^ 2) * T) ≤
          Real.exp (-(2 / (d / 2) ^ 2) * s) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have himLower :
          z.im * Real.exp (-(2 / (d / 2) ^ 2) * T) ≤ y.im := by
        exact (mul_le_mul_of_nonneg_left hexp hzim.le).trans himRaw
      have hlowerPos :
          0 < z.im * Real.exp (-(2 / (d / 2) ^ 2) * T) :=
        mul_pos hzim (Real.exp_pos _)
      have hstepY : u < y.im ^ 2 / 8 := by
        calc
          u < (z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)) ^ 2 / 8 := hstep
          _ ≤ y.im ^ 2 / 8 := by nlinarith
      have hWshift : Continuous (fun r ↦ W (s + r)) :=
        hWcont.comp (continuous_const.add continuous_id)
      obtain ⟨curve, hcurve0, hcurveDeriv, hcurveStrip⟩ :=
        loewner_local_existence_strip_explicit hWshift hypos
      let hfull : LoewnerForwardSolution (fun r ↦ W (s + r)) y
          (y.im ^ 2 / 8) :=
        { curve := curve
          initial := hcurve0
          deriv := hcurveDeriv
          upper := by
            intro r hr
            exact loewnerStrip_subset_upperHalfPlane (by positivity)
              (hcurveStrip r hr) }
      let hseg : LoewnerForwardSolution (fun r ↦ W (s + r)) y u :=
        hfull.restrict hstepY.le
      let gh : LoewnerForwardSolution W z (s + u) :=
        g.append hseg hs0 hu
      have htime : (((n + 1 : ℕ) : ℝ) * u) = s + u := by
        simp only [s, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [htime]
      exact ⟨gh⟩


theorem exists_loewnerForwardSolution_of_driverBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {T M d : ℝ}
    (hT : 0 ≤ T) (hd : 0 < d) {z : ℂ}
    (hzim : 0 < z.im) (hzre : M + d ≤ z.re)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M) :
    Nonempty (LoewnerForwardSolution W z T) := by
  let δ : ℝ := z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * T / δ ^ 2)
  have hquot : 0 ≤ 8 * T / δ ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := T / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = T := by
    dsimp [u]
    field_simp
  have hstep : u < δ ^ 2 / 8 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 8 * T < (n : ℝ) * δ ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hn
    nlinarith
  have hg := exists_loewnerForwardSolution_steps_of_driverBarrier
    hWcont hd hu hzim hzre hW (by simpa [δ] using hstep) n hnu.le
  rwa [hnu] at hg


theorem exists_loewnerForwardSolution_of_driverLowerBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {T m d : ℝ}
    (hT : 0 ≤ T) (hd : 0 < d) {z : ℂ}
    (hzim : 0 < z.im) (hzre : z.re ≤ m - d)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, m ≤ W s) :
    Nonempty (LoewnerForwardSolution W z T) := by
  have hzreflect : -m + d ≤ (loewnerReflection z).re := by
    simp only [loewnerReflection_re]
    linarith
  have hWreflect : ∀ s ∈ Icc (0 : ℝ) T, -W s ≤ -m := by
    intro s hs
    linarith [hW s hs]
  have hzimreflect : 0 < (loewnerReflection z).im := by
    simpa only [loewnerReflection_im] using hzim
  obtain ⟨g⟩ := exists_loewnerForwardSolution_of_driverBarrier
    (W := fun s ↦ -W s) (z := loewnerReflection z) (M := -m)
    hWcont.neg hT hd hzimreflect hzreflect hWreflect
  refine ⟨?_⟩
  simpa only [neg_neg, loewnerReflection_involutive] using g.reflect


end StatMech.SLE
