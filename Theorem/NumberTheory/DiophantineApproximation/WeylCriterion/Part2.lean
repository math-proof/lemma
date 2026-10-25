/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Weyl's equidistribution criterion: a real sequence is equidistributed modulo 1
if and only if every nontrivial Fourier mean vanishes.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Def.NumberTheory.DiophantineApproximation.WeylCriterion.Part2
open scoped BigOperators
open Filter Topology


namespace MetaMathlibExt

lemma wcF_integral (a b δ : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, wcF a b δ ha0 hb1 hδ ((t : ℝ) : AddCircle (1 : ℝ))) =
      ((∫ t in (0 : ℝ)..1, wcPhi a b δ t : ℝ) : ℂ) := by
  classical
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  have hIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
  rw [hIcc]
  intro t ht
  rw [Set.mem_Icc] at ht
  by_cases ht1 : t = 1
  · subst ht1
    have h10 : ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
      have h1 : ((1 : ℝ) : AddCircle (1 : ℝ)) - ((0 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        have hzero : ((((1 : ℤ)) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
          rw [AddCircle.coe_eq_zero_iff (1 : ℝ)]
          exact ⟨1, by rw [zsmul_eq_mul, mul_one]⟩
        have c0 : ((0 : ℝ) : AddCircle (1 : ℝ)) = 0 := AddCircle.coe_zero (1 : ℝ)
        have c1 : ((((1 : ℤ)) : ℝ) : AddCircle (1 : ℝ)) =
            ((1 : ℝ) : AddCircle (1 : ℝ)) := by
          norm_cast
        rw [c0, sub_zero, ← c1]
        exact hzero
      exact sub_eq_zero.mp h1
    change (wcF a b δ ha0 hb1 hδ ((1 : ℝ) : AddCircle (1 : ℝ))) =
      ((wcPhi a b δ 1 : ℝ) : ℂ)
    rw [h10]
    rw [wcF_coe a b δ ha0 hb1 hδ 0 ⟨le_refl _, one_pos⟩]
    rw [wcPhi_eq_zero_of_le a b δ 0 hδ ha0,
      wcPhi_eq_zero_of_ge a b δ 1 hδ hb1]
  · exact wcF_coe a b δ ha0 hb1 hδ t
      ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩

/-- Lower bound for interval frequencies. -/
lemma wc_lower (x : ℕ → ℝ)
    (hfour : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
        atTop (nhds 0))
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, b - a - ε ≤
      ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
        (Finset.range N)).card : ℝ) / (N : ℝ) := by
  classical
  set δ := min (ε / 2) ((b - a) / 2) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    apply div_pos _ (by norm_num)
    exact lt_min (by linarith) (by linarith)
  have h2δ : 2 * δ < b - a := by
    rw [hδdef]
    have h1 : min (ε / 2) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
    linarith
  have h2δε : 2 * δ ≤ ε / 2 := by
    rw [hδdef]
    have h1 : min (ε / 2) ((b - a) / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  have hF := wc_all_cont x hfour (wcF a b δ ha0 hb1 hδpos)
  rw [wcF_integral a b δ ha0 hb1 hδpos] at hF
  have hR : Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        wcPhi a b δ (Int.fract (x n)))
      atTop (nhds (∫ t in (0 : ℝ)..1, wcPhi a b δ t)) := by
    have hre := (Complex.continuous_re.tendsto _).comp hF
    have elim : Complex.re
        (((∫ t in (0 : ℝ)..1, wcPhi a b δ t : ℝ) : ℂ)) =
        (∫ t in (0 : ℝ)..1, wcPhi a b δ t) := by simp
    rw [elim] at hre
    have efun : ∀ N : ℕ, Complex.re ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        wcF a b δ ha0 hb1 hδpos ((x n : ℝ) : AddCircle (1 : ℝ))) =
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
          wcPhi a b δ (Int.fract (x n)) := by
      intro N
      have e1 : (∑ n ∈ Finset.range N,
          wcF a b δ ha0 hb1 hδpos ((x n : ℝ) : AddCircle (1 : ℝ))) =
          (((∑ n ∈ Finset.range N, wcPhi a b δ (Int.fract (x n)) : ℝ)) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl
          (fun n _ => wcF_fract a b δ ha0 hb1 hδpos (x n))
      have e2' : (1 / (N : ℂ)) = (((1 / (N : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      have ere : ∀ z : ℝ, Complex.re (((z : ℝ)) : ℂ) = z := fun z => by simp
      rw [e1, e2', ← Complex.ofReal_mul, ere]
    have efun2 : (Complex.re ∘ (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        wcF a b δ ha0 hb1 hδpos ((x n : ℝ) : AddCircle (1 : ℝ)))) =
        (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
          wcPhi a b δ (Int.fract (x n))) :=
      funext efun
    rwa [efun2] at hre
  have hL := wcPhi_integral_ge a b δ ha0 hab hb1 hδpos h2δ
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hR) (ε / 2) (by linarith)
  have main : ∀ᶠ N in atTop, b - a - ε ≤ (wcCnt x a b N : ℝ) / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hN0 : N ≥ N₀ := le_trans (Nat.le_max_left _ _) hN
    have hNge1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
    have h1 := hN₀ N hN0
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have havg_gt : (∫ t in (0 : ℝ)..1, wcPhi a b δ t) - ε / 2 <
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
          wcPhi a b δ (Int.fract (x n)) := by
      have h' := (abs_lt.mp h1).1
      linarith
    have hNr : (0 : ℝ) < (N : ℝ) := by
      have hNe : 0 < N := by omega
      exact_mod_cast hNe
    have hle : (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        wcPhi a b δ (Int.fract (x n)) ≤ (wcCnt x a b N : ℝ) / (N : ℝ) := by
      have hsum := wcPhi_sum_le x a b δ hδpos N
      calc (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
              wcPhi a b δ (Int.fract (x n))
          ≤ (1 / (N : ℝ)) * (wcCnt x a b N : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (wcCnt x a b N : ℝ) / (N : ℝ) := by
            conv_rhs => rw [div_eq_mul_one_div]
            exact mul_comm _ _
    linarith [havg_gt, hL, hle, h2δε]
  exact main

/-- Backward direction (Fourier means vanish implies equidistribution). -/
lemma wc_backward (x : ℕ → ℝ)
    (hfour : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
        atTop (nhds 0))
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) :
    Tendsto (fun N : ℕ =>
      ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
        (Finset.range N)).card : ℝ) / (N : ℝ))
      atTop (nhds (b - a)) := by
  have hsum : ∀ N : ℕ, wcCnt x 0 a N + wcCnt x a b N + wcCnt x b 1 N = N := by
    intro N
    have hpart : Finset.filter
          (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
          (Finset.range N) ∪
        (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N) ∪
          Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)) =
        Finset.range N := by
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hnN, _⟩ | (⟨hnN, _⟩ | ⟨hnN, _⟩))
        · exact hnN
        · exact hnN
        · exact hnN
      · intro hnN
        have hy0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
        have hy1 : Int.fract (x n) < 1 := Int.fract_lt_one _
        rcases lt_or_ge (Int.fract (x n)) a with hya | hya
        · exact Or.inl ⟨hnN, hy0, hya⟩
        · rcases lt_or_ge (Int.fract (x n)) b with hyb | hyb
          · exact Or.inr (Or.inl ⟨hnN, hya, hyb⟩)
          · exact Or.inr (Or.inr ⟨hnN, hyb, hy1⟩)
    have hdisj2 : Disjoint
        (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N))
        (Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)) := by
      rw [Finset.disjoint_filter]
      intro n _ h1 h2
      linarith [h1.2, h2.1]
    have hdisj1 : Disjoint
        (Finset.filter
          (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
          (Finset.range N))
        (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N) ∪
          Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)) := by
      rw [Finset.disjoint_union_right]
      constructor
      · rw [Finset.disjoint_filter]
        intro n _ h1 h2
        linarith [h1.2, h2.1]
      · rw [Finset.disjoint_filter]
        intro n _ h1 h2
        linarith [h1.2, h2.1, hab]
    have hcard : (Finset.filter
        (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
        (Finset.range N)).card +
        ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N)).card +
        (Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)).card) = (Finset.range N).card := by
      have e := congrArg Finset.card hpart
      rwa [Finset.card_union_of_disjoint hdisj1,
        Finset.card_union_of_disjoint hdisj2] at e
    have hcr : (Finset.range N).card = N := Finset.card_range N
    have eL : wcCnt x 0 a N = (Finset.filter
        (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
        (Finset.range N)).card := by rfl
    have eM : wcCnt x a b N = (Finset.filter
        (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
        (Finset.range N)).card := by rfl
    have eR : wcCnt x b 1 N = (Finset.filter
        (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
        (Finset.range N)).card := by rfl
    omega
  have hlow_mid : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      b - a - ε ≤ (wcCnt x a b N : ℝ) / (N : ℝ) :=
    fun ε hε => wc_lower x hfour a b ha0 hab hb1 ε hε
  have hlow_left : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      a - 0 - ε ≤ (wcCnt x 0 a N : ℝ) / (N : ℝ) := by
    intro ε hε
    by_cases ha : 0 < a
    · have ha1 : a ≤ 1 := le_trans (le_of_lt hab) hb1
      exact wc_lower x hfour 0 a le_rfl ha ha1 ε hε
    · have ha0' : a = 0 := le_antisymm (not_lt.mp ha) ha0
      filter_upwards with N
      have hzero : wcCnt x 0 0 N = 0 := by
        have hemp : Finset.filter
            (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 0)
            (Finset.range N) = ∅ := by
          apply Finset.filter_false_of_mem
          intro n _ hn
          linarith [hn.1, hn.2]
        have e : wcCnt x 0 0 N = (Finset.filter
            (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 0)
            (Finset.range N)).card := by rfl
        rw [e, hemp, Finset.card_empty]
      rw [ha0', hzero]
      simp only [Nat.cast_zero, zero_div, sub_zero, zero_sub]
      exact neg_nonpos.mpr (le_of_lt hε)
  have hlow_right : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      1 - b - ε ≤ (wcCnt x b 1 N : ℝ) / (N : ℝ) := by
    intro ε hε
    by_cases hb : b < 1
    · have hb0 : 0 ≤ b := le_trans ha0 (le_of_lt hab)
      exact wc_lower x hfour b 1 hb0 hb le_rfl ε hε
    · have hb1' : b = 1 := le_antisymm hb1 (not_lt.mp hb)
      filter_upwards with N
      have hzero : wcCnt x 1 1 N = 0 := by
        have hemp : Finset.filter
            (fun n => (1 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
            (Finset.range N) = ∅ := by
          apply Finset.filter_false_of_mem
          intro n _ hn
          linarith [hn.1, hn.2]
        have e : wcCnt x 1 1 N = (Finset.filter
            (fun n => (1 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
            (Finset.range N)).card := by rfl
        rw [e, hemp, Finset.card_empty]
      rw [hb1', hzero]
      simp only [Nat.cast_zero, zero_div, sub_self, zero_sub]
      exact neg_nonpos.mpr (le_of_lt hε)
  have hdiv : ∀ N : ℕ, 1 ≤ N →
      (wcCnt x a b N : ℝ) / (N : ℝ) =
        1 - (wcCnt x 0 a N : ℝ) / (N : ℝ) - (wcCnt x b 1 N : ℝ) / (N : ℝ) := by
    intro N hN
    have hNr : (N : ℝ) ≠ 0 := by
      have hNe : N ≠ 0 := by omega
      exact_mod_cast hNe
    have hsumR : (wcCnt x 0 a N : ℝ) + (wcCnt x a b N : ℝ) +
        (wcCnt x b 1 N : ℝ) = (N : ℝ) := by
      exact_mod_cast hsum N
    have e : (wcCnt x a b N : ℝ) / (N : ℝ) =
        ((N : ℝ) - (wcCnt x 0 a N : ℝ) - (wcCnt x b 1 N : ℝ)) / (N : ℝ) := by
      congr 1
      linarith [hsumR]
    rw [e, sub_div, sub_div, div_self hNr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlo_mid := hlow_mid (ε / 3) (by linarith)
  have hlo_L := hlow_left (ε / 3) (by linarith)
  have hlo_R := hlow_right (ε / 3) (by linarith)
  have hev := hlo_mid.and (hlo_L.and (hlo_R.and (eventually_ge_atTop 1)))
  rw [eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hmid, hL, hR, hN1⟩ := hN₀ N hN
  have hN : 1 ≤ N := hN1
  have hup : (wcCnt x a b N : ℝ) / (N : ℝ) ≤ b - a + 2 * (ε / 3) := by
    rw [hdiv N hN]
    linarith [hL, hR]
  change dist ((wcCnt x a b N : ℝ) / (N : ℝ)) (b - a) < ε
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor
  · linarith [hmid]
  · linarith [hup]

/-- Weyl's equidistribution criterion (statement `weyl-criterion-s1`):
a real sequence `x` is equidistributed mod 1 iff every nontrivial Fourier mean
vanishes. Source: https://en.wikipedia.org/wiki/Equidistribution_theorem.

Proves `Wanted` entry `weyl_criterion`. -/
theorem weyl_criterion (x : ℕ → ℝ) :
    (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N : ℕ =>
        ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N)).card : ℝ) / (N : ℝ))
        atTop (nhds (b - a)))
    ↔ ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ =>
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          Complex.exp (((2 * Real.pi * (h : ℝ) * x n : ℝ) : ℂ) * Complex.I))
        atTop (nhds 0) := by
  constructor
  · intro heq h hh
    exact wc_forward x heq h hh
  · intro hfour a b ha0 hab hb1
    exact wc_backward x hfour a b ha0 hab hb1

end MetaMathlibExt
