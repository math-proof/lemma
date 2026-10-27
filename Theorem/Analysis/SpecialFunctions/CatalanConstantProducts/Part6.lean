/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part6


section

namespace MetaMathlibExt

theorem ccp_alt_sum_add_pair (a : ℕ → ℝ) (m : ℕ) :
    ccp_alt_sum a (2 * (m + 1)) =
      ccp_alt_sum a (2 * m) + a (2 * m) - a (2 * m + 1) := by
  have heven : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul]
    norm_num
  have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  unfold ccp_alt_sum
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, heven, hodd]
  ring

theorem ccp_alt_sum_even_bounds (a : ℕ → ℝ) (ha : Antitone a) (m : ℕ) :
    0 ≤ ccp_alt_sum a (2 * m) ∧
      ccp_alt_sum a (2 * m) + a (2 * m) ≤ a 0 := by
  induction m with
  | zero =>
      simp [ccp_alt_sum]
  | succ m ih =>
      have hpair : a (2 * m + 1) ≤ a (2 * m) := ha (by omega)
      have hnext : a (2 * (m + 1)) ≤ a (2 * m + 1) := ha (by omega)
      constructor
      · rw [ccp_alt_sum_add_pair]
        linarith [ih.1]
      · rw [ccp_alt_sum_add_pair]
        linarith [ih.2]

theorem ccp_alt_sum_bounds (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k)
    (ha : Antitone a) (N : ℕ) :
    0 ≤ ccp_alt_sum a N ∧ ccp_alt_sum a N ≤ a 0 := by
  rcases N.even_or_odd' with ⟨m, hm | hm⟩
  · subst N
    have h := ccp_alt_sum_even_bounds a ha m
    constructor
    · exact h.1
    · linarith [ha0 (2 * m)]
  · subst N
    have h := ccp_alt_sum_even_bounds a ha m
    have heven : (-1 : ℝ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      norm_num
    have hsum : ccp_alt_sum a (2 * m + 1) =
        ccp_alt_sum a (2 * m) + a (2 * m) := by
      unfold ccp_alt_sum
      rw [Finset.sum_range_succ, heven, one_mul]
    rw [hsum]
    exact ⟨add_nonneg h.1 (ha0 (2 * m)), h.2⟩

theorem ccp_catFint_eq_alt_sum (N : ℕ) (u : ℝ) :
    catFint N u = ccp_alt_sum (ccp_term u) N := by
  rw [catFint_eq_range]
  unfold ccp_alt_sum ccp_term
  rfl

theorem ccp_term_zero_le_one (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ccp_term u 0 ≤ 1 := by
  have hub : u ^ 2 ≤ 1 := by
    have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      u ^ 2 = |u| ^ 2 := by rw [sq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 1 := one_pow 2
  have hden : 0 < (4 : ℝ) - u ^ 2 := by linarith
  rw [ccp_term]
  norm_num only [zero_add, Nat.cast_one, one_pow, mul_one]
  exact (div_le_one hden).2 (by linarith)

theorem ccp_catFint_norm_le_one (N : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖catFint N u‖ ≤ 1 := by
  have hbounds := ccp_alt_sum_bounds (ccp_term u)
    (fun k => ccp_term_nonneg u k hu0 hu1) (ccp_term_antitone u hu0 hu1) N
  rw [← ccp_catFint_eq_alt_sum] at hbounds
  rw [Real.norm_eq_abs, abs_of_nonneg hbounds.1]
  exact hbounds.2.trans (ccp_term_zero_le_one u hu0 hu1)

/-- Summability of alternating terms for fixed `u`. -/
theorem catFint_summable (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k * (u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)))) := by
  have hbound : ∀ k : ℕ,
      ‖(-1 : ℝ) ^ k * (u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)))‖
        ≤ 1 / (3 * (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hub : u ^ 2 ≤ 1 := by
      have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := by
            exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = 1 := one_pow 2
    have hden : (3 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ 2)
        ≤ 4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2 := by
      have hm : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
        have h1 : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
              exact pow_le_pow_left₀ (by norm_num) h1 2
      linarith
    have hpos : (0 : ℝ) < 4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2 := by
      have hm : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
        have h1 : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
              exact pow_le_pow_left₀ (by norm_num) h1 2
      linarith [hden, hm]
    have hnonneg : (0 : ℝ) ≤ u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)) := by
      apply div_nonneg (sq_nonneg _) (le_of_lt hpos)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h1 : u ^ 2 * (3 * (((k + 1 : ℕ) : ℝ) ^ 2))
        ≤ 1 * (4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2) := by
      nlinarith [hub, hden, sq_nonneg u]
    linarith [h1]
  have hsumm : Summable (fun k : ℕ => 1 / (3 * (((k + 1 : ℕ) : ℝ) ^ 2))) := by
    have hbase : Summable (fun k : ℕ => 1 / ((((k + 1 : ℕ) : ℝ) ^ 2))) := by
      have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      exact (summable_nat_add_iff 1).mpr h1
    have heq : (fun k : ℕ => 1 / (3 * (((k + 1 : ℕ) : ℝ) ^ 2)))
        = (fun k : ℕ => (1 / 3 : ℝ) * (1 / ((((k + 1 : ℕ) : ℝ) ^ 2)))) := by
      funext k
      rw [← one_div_mul_one_div]
    rw [heq]
    exact hbase.mul_left (1 / 3)
  exact Summable.of_norm_bounded hsumm hbound

/-- Doubling tends to infinity. -/
theorem catTwoMul_tendsto :
    Filter.Tendsto (fun m : ℕ => 2 * m) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun m hm => by omega⟩

/-- Finite integrands vanish at zero. -/
theorem catFint_zero (N : ℕ) : catFint N 0 = 0 := by
  unfold catFint
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    mul_zero, Finset.sum_const_zero]

/-- Infinite alternating sum equals the cosecant limit. -/
theorem catTsum_eq_flim (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∑' k : ℕ, (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
      = catFlim u := by
  have hu0' : 0 ≤ u := le_of_lt hu0
  have hne_u : u ≠ 0 := ne_of_gt hu0
  have hub : u ^ 2 ≤ 1 := by
    have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 1 := one_pow 2
  have hsin : 0 < Real.sin (Real.pi * (u / 2)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have hpi : 0 < Real.pi := Real.pi_pos
      have h2 : (0 : ℝ) < u / 2 := by linarith
      exact mul_pos hpi h2
    · have hpi : 0 < Real.pi := Real.pi_pos
      have h2 : u / 2 < 1 := by linarith
      calc Real.pi * (u / 2) < Real.pi * 1 := by
            apply mul_lt_mul_of_pos_left h2 hpi
        _ = Real.pi := mul_one _
  have hsin_ne : Real.sin (Real.pi * (u / 2)) ≠ 0 := ne_of_gt hsin
  have hf : Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2))) :=
    catFint_summable u hu0' hu1
  have hc : u ^ 2 / 4 ≠ 0 := by positivity
  have hfg : (fun k : ℕ => (-1 : ℝ) ^ k * (u ^ 2 /
      (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
      = (fun k : ℕ => (u ^ 2 / 4) *
        (((-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))))) := by
    funext k
    set A : ℝ := ((((k + 1 : ℕ)) : ℝ) ^ 2) with hA
    have hm : (1 : ℝ) ≤ A := by
      rw [hA]
      have h1 : (1 : ℝ) ≤ ((((k + 1 : ℕ)) : ℝ)) := by
        have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
        exact_mod_cast this
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ ((((k + 1 : ℕ)) : ℝ) ^ 2) := pow_le_pow_left₀ (by norm_num) h1 2
    have hpos : (0 : ℝ) < 4 * A - u ^ 2 := by rw [hA] at hm ⊢; linarith
    have hpos2 : (0 : ℝ) < A - (u / 2) ^ 2 := by
      have : A - (u / 2) ^ 2 = (4 * A - u ^ 2) / 4 := by ring
      rw [this]
      linarith
    have n1 : 4 * A - u ^ 2 ≠ 0 := ne_of_gt hpos
    have n2 : A - (u / 2) ^ 2 ≠ 0 := ne_of_gt hpos2
    have hX : u ^ 2 / (4 * A - u ^ 2) = (u ^ 2 / 4) / (A - (u / 2) ^ 2) := by
      rw [div_eq_div_iff n1 n2]
      ring
    calc (-1 : ℝ) ^ k * (u ^ 2 / (4 * A - u ^ 2))
        = (-1 : ℝ) ^ k * ((u ^ 2 / 4) / (A - (u / 2) ^ 2)) := by rw [hX]
      _ = (u ^ 2 / 4) * ((-1 : ℝ) ^ k / (A - (u / 2) ^ 2)) := by ring
  have hg : Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
    have hmul := hf.mul_left (4 / u ^ 2)
    have heq : (fun k : ℕ => (4 / u ^ 2) * ((-1 : ℝ) ^ k *
        (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2))))
        = (fun k : ℕ =>
          (-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
      funext k
      set A : ℝ := ((((k + 1 : ℕ)) : ℝ) ^ 2) with hA
      have hm : (1 : ℝ) ≤ A := by
        rw [hA]
        have h1 : (1 : ℝ) ≤ ((((k + 1 : ℕ)) : ℝ)) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ ((((k + 1 : ℕ)) : ℝ) ^ 2) := pow_le_pow_left₀ (by norm_num) h1 2
      have hpos : (0 : ℝ) < 4 * A - u ^ 2 := by rw [hA] at hm ⊢; linarith
      have hpos2 : (0 : ℝ) < A - (u / 2) ^ 2 := by
        have : A - (u / 2) ^ 2 = (4 * A - u ^ 2) / 4 := by ring
        rw [this]
        linarith
      have n1 : 4 * A - u ^ 2 ≠ 0 := ne_of_gt hpos
      have n2 : A - (u / 2) ^ 2 ≠ 0 := ne_of_gt hpos2
      have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hne_u
      have hX : u ^ 2 / (4 * A - u ^ 2) = (u ^ 2 / 4) / (A - (u / 2) ^ 2) := by
        rw [div_eq_div_iff n1 n2]
        ring
      have hcancel : (4 / u ^ 2) * (u ^ 2 / 4) = 1 := by
        field_simp
      calc (4 / u ^ 2) * ((-1 : ℝ) ^ k * (u ^ 2 / (4 * A - u ^ 2)))
          = (-1 : ℝ) ^ k * ((4 / u ^ 2) * (u ^ 2 / (4 * A - u ^ 2))) := by ring
        _ = (-1 : ℝ) ^ k * ((4 / u ^ 2) * ((u ^ 2 / 4) / (A - (u / 2) ^ 2))) := by rw [hX]
        _ = (-1 : ℝ) ^ k * (((4 / u ^ 2) * (u ^ 2 / 4)) / (A - (u / 2) ^ 2)) := by ring
        _ = (-1 : ℝ) ^ k / (A - (u / 2) ^ 2) := by rw [hcancel, mul_one_div]
    rw [heq] at hmul
    exact hmul
  have htsum := catCsc_real_tsum u hu0 hu1
  have hmul : (∑' k : ℕ, (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
      = (u ^ 2 / 4) * ∑' k : ℕ, ((-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
    rw [hfg, tsum_mul_left]
  rw [hmul, htsum]
  have hflim : catFlim u = Real.pi * u / (4 * Real.sin (Real.pi * u / 2)) - 1 / 2 := by
    unfold catFlim
    simp only [hne_u, ite_false]
  rw [hflim]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu2 : (u / 2 : ℝ) ≠ 0 := by linarith
  have h2u : (2 : ℝ) * (u / 2) ≠ 0 := by linarith
  field_simp
  ring

/-- Finite integrands converge pointwise to the cosecant limit. -/
theorem catFint_tendsto (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Filter.Tendsto (fun m : ℕ => catFint (2 * m) u) Filter.atTop
      (nhds (catFlim u)) := by
  by_cases hu : u = 0
  · subst hu
    simp only [catFint_zero]
    have hflim : catFlim 0 = 0 := by
      unfold catFlim
      simp
    rw [hflim]
    exact tendsto_const_nhds
  · have hu0' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hf := catFint_summable u hu0 hu1
    have hlim : Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
        Filter.atTop
        (nhds (∑' k : ℕ, (-1 : ℝ) ^ k *
          (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))) :=
      hf.hasSum.tendsto_sum_nat
    have hcomp := hlim.comp catTwoMul_tendsto
    rw [catTsum_eq_flim u hu0' hu1] at hcomp
    refine Filter.Tendsto.congr (fun m => ?_) hcomp
    rw [catFint_eq_range]
    rfl

theorem ccp_catFint_integral_tendsto :
    Filter.Tendsto (fun m : ℕ => ∫ u in (0 : ℝ)..1, catFint (2 * m) u)
      Filter.atTop (nhds (∫ u in (0 : ℝ)..1, catFlim u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · refine Filter.Eventually.of_forall fun m => ?_
    have hmeas : Measurable (fun u : ℝ => catFint (2 * m) u) := by
      unfold catFint
      fun_prop
    exact hmeas.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun m => ?_
    filter_upwards [] with u
    intro hu
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hu
    exact ccp_catFint_norm_le_one (2 * m) u hu.1.le hu.2
  · exact intervalIntegrable_const
  · filter_upwards [] with u
    intro hu
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hu
    exact catFint_tendsto u hu.1.le hu.2

end MetaMathlibExt
end
