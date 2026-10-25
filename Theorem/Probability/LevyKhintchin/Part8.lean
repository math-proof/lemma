/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.Probability.LevyKhintchin.Part8
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_exists_charFun_root {μ : Measure ℝ}
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ t : ℝ, charFun μ t = charFun ρ t ^ n := by
  obtain ⟨ρ, hρ, hμ⟩ := hID n hn
  have h_pow := lkConvPow_succ_iterate ρ (n - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at h_pow
  refine ⟨ρ, hρ, fun t ↦ ?_⟩
  rw [hμ, ← h_pow, lk_charFun_convPow]

lemma lk_charFun_ne_zero_double {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {t : ℝ} (ht : charFun μ t ≠ 0) : charFun μ (2 * t) ≠ 0 := by
  have hpos : 0 < ‖charFun μ t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ht)
  obtain ⟨n, hnsmall⟩ := exists_pow_lt_of_lt_one hpos (show (3 / 4 : ℝ) < 1 by norm_num)
  have hnorm_le : ‖charFun μ t‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (charFun μ t), norm_charFun_le_one (μ := μ) t]
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    change 1 < ‖charFun μ t‖ ^ 2 at hnsmall
    exact (not_lt_of_ge hnorm_le) hnsmall
  obtain ⟨ρ, hρ, hroot⟩ := lk_exists_charFun_root hID hn
  have hnorm : ‖charFun μ t‖ = ‖charFun ρ t‖ ^ n := by
    rw [hroot t, norm_pow]
  have hsq : ‖charFun μ t‖ ^ 2 = (‖charFun ρ t‖ ^ 2) ^ n := by
    rw [hnorm, ← pow_mul, Nat.mul_comm, pow_mul]
  have hroot_large : (3 / 4 : ℝ) < ‖charFun ρ t‖ ^ 2 := by
    by_contra h
    have hp := pow_le_pow_left₀ (sq_nonneg ‖charFun ρ t‖) (le_of_not_gt h) n
    have hle : ‖charFun μ t‖ ^ 2 ≤ (3 / 4 : ℝ) ^ n := hsq.trans_le hp
    exact (not_lt_of_ge hle) hnsmall
  have hroot_double : charFun ρ (2 * t) ≠ 0 := by
    intro hzero
    have hineq := lk_one_sub_norm_charFun_sq_two_le ρ t
    rw [hzero, norm_zero] at hineq
    norm_num at hineq
    nlinarith
  rw [hroot (2 * t)]
  exact pow_ne_zero n hroot_double

lemma lk_charFun_ne_zero_two_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {t : ℝ} (ht : charFun μ t ≠ 0) (m : ℕ) :
    charFun μ ((2 : ℝ) ^ m * t) ≠ 0 := by
  induction m with
  | zero => simpa using ht
  | succ m ih =>
      have heq : (2 : ℝ) ^ (m + 1) * t = 2 * ((2 : ℝ) ^ m * t) := by
        rw [pow_succ]
        ac_rfl
      rw [heq]
      exact lk_charFun_ne_zero_double hID ih

lemma lk_charFun_ne_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    (t : ℝ) : charFun μ t ≠ 0 := by
  have hlocal : ∀ᶠ x : ℝ in 𝓝 0, charFun μ x ≠ 0 := by
    have hopen : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
    have hmem : charFun μ 0 ∈ ({0}ᶜ : Set ℂ) := by simp
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (MeasureTheory.continuous_charFun (μ := μ)).continuousAt.eventually
        (hopen.mem_nhds hmem)
  have hseq : Filter.Tendsto (fun m : ℕ ↦ t / (2 : ℝ) ^ m) Filter.atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show 0 ≤ (2 : ℝ)⁻¹ by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num)).const_mul t
  obtain ⟨m, hm⟩ := (hseq.eventually hlocal).exists
  have h := lk_charFun_ne_zero_two_pow hID hm m
  have hpow : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have heq : (2 : ℝ) ^ m * (t / (2 : ℝ) ^ m) = t := by
    field_simp
  simpa only [heq] using h

lemma lk_exists_distinguishedLog {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L 0 = 0 ∧
      ∀ t : ℝ, Complex.exp (L t) = charFun μ t := by
  have hU : IsSimplyConnected (Set.univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  have hne : 0 ∉ charFun μ '' (Set.univ : Set ℝ) := by
    rintro ⟨t, -, ht⟩
    exact lk_charFun_ne_zero hID t ht
  obtain ⟨l, hl, hlexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    (MeasureTheory.continuous_charFun (μ := μ)).continuousOn hne
  have hlc : Continuous l := continuousOn_univ.mp hl
  have hlexp' (t : ℝ) : Complex.exp (l t) = charFun μ t := by
    simpa only [Function.comp_apply] using hlexp (Set.mem_univ t)
  let L : ℝ → ℂ := fun t ↦ l t - l 0
  refine ⟨L, hlc.sub continuous_const, by simp [L], fun t ↦ ?_⟩
  change Complex.exp (l t - l 0) = charFun μ t
  rw [Complex.exp_sub, hlexp' t, hlexp' 0]
  simp

lemma lk_exists_exp_root {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {L : ℝ → ℂ} (hL : Continuous L) (hL0 : L 0 = 0)
    (hLexp : ∀ t : ℝ, Complex.exp (L t) = charFun μ t)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ t : ℝ, charFun ρ t = Complex.exp (L t / (n : ℝ)) := by
  obtain ⟨ρ, hρ, hroot⟩ := lk_exists_charFun_root hID hn
  exact ⟨ρ, hρ, lk_charFun_root_eq_exp_div hL hL0 hLexp hn hroot⟩

end MetaMathlibExt
