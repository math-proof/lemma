/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.Part1Ch9Entry1Logratio.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry1Logratio

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem entry1_oddLimit_continuous (r : ℕ) (a : ℝ) :
    Continuous (fun x : ℝ => entry1_oddLimit r a x) := by
  unfold entry1_oddLimit
  apply continuous_finsetSum
  intro k _
  have hF : ((2 * k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  exact (((continuous_const.mul continuous_const).mul
    (continuous_id.pow _)).div continuous_const (fun _ => hF))

theorem entry1_evenLimit_continuous (r : ℕ) (a : ℝ) :
    Continuous (fun x : ℝ => entry1_evenLimit r a x) := by
  unfold entry1_evenLimit
  apply continuous_finsetSum
  intro k _
  have hF : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  exact (((continuous_const.mul continuous_const).mul
    (continuous_id.pow _)).div continuous_const (fun _ => hF))

theorem entry1_evenLimit_eq_integral (r : ℕ) (a x : ℝ)
    (hr2 : 2 ≤ r) :
    entry1_evenLimit r a x =
      ∫ t in (0 : ℝ)..x, entry1_oddLimit (r - 1) a t := by
  have hrange : r / 2 = (r - 1 - 1) / 2 + 1 := by omega
  unfold entry1_evenLimit entry1_oddLimit
  rw [← hrange]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hidx : (r - 1) - 2 * k = r - 2 * k - 1 := by omega
    rw [hidx]
    have hF0 : ((2 * k).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hF1 : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hfact : ((2 * k + 1).factorial : ℝ) =
        ((2 * k + 1 : ℕ) : ℝ) * ((2 * k).factorial : ℝ) := by
      rw [show 2 * k + 1 = (2 * k) + 1 from rfl, Nat.factorial_succ]
      push_cast
      ring
    have hfun : (fun t : ℝ => (-1 : ℝ) ^ k *
        chapter9Entry1Constant (r - 2 * k - 1) a * t ^ (2 * k) /
        ((2 * k).factorial : ℝ)) =
        (fun t : ℝ => (((-1 : ℝ) ^ k *
          chapter9Entry1Constant (r - 2 * k - 1) a /
          ((2 * k).factorial : ℝ))) * t ^ (2 * k)) := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul, entry1_integral_pow]
    have hcast : ((2 * k : ℕ) : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, hfact]
    field_simp
  · intro k _
    have hF0 : ((2 * k).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hcont : Continuous (fun t : ℝ => (-1 : ℝ) ^ k *
        chapter9Entry1Constant (r - 1 - 2 * k) a * t ^ (2 * k) /
        ((2 * k).factorial : ℝ)) :=
      (((continuous_const.mul continuous_const).mul
        (continuous_id.pow _)).div continuous_const (fun _ => hF0))
    exact hcont.intervalIntegrable 0 x

theorem entry1_oddLimit_eq (r : ℕ) (a x : ℝ) :
    entry1_oddLimit r a x = chapter9Entry1Constant r a -
      ∫ t in (0 : ℝ)..x, entry1_evenLimit (r - 1) a t := by
  unfold entry1_oddLimit entry1_evenLimit
  rw [Finset.sum_range_succ']
  have hf0 : (-1 : ℝ) ^ 0 * chapter9Entry1Constant (r - 2 * 0) a *
      x ^ (2 * 0) / ((2 * 0).factorial : ℝ) =
      chapter9Entry1Constant r a := by
    simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, one_mul, div_one]
  rw [hf0]
  have hInt : (∫ t in (0 : ℝ)..x, ∑ k ∈ range ((r - 1) / 2),
      (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 1 - 2 * k - 1) a *
        t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) =
      ∑ k ∈ range ((r - 1) / 2), ∫ t in (0 : ℝ)..x,
        (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 1 - 2 * k - 1) a *
          t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
    apply intervalIntegral.integral_finsetSum
    intro k _
    have hF : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hcont : Continuous (fun t : ℝ => (-1 : ℝ) ^ k *
        chapter9Entry1Constant (r - 1 - 2 * k - 1) a * t ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) :=
      (((continuous_const.mul continuous_const).mul
        (continuous_id.pow _)).div continuous_const (fun _ => hF))
    exact hcont.intervalIntegrable 0 x
  rw [hInt]
  have hper : ∀ k ∈ range ((r - 1) / 2),
      (-1 : ℝ) ^ (k + 1) * chapter9Entry1Constant (r - 2 * (k + 1)) a *
        x ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) =
      -∫ t in (0 : ℝ)..x, (-1 : ℝ) ^ k *
        chapter9Entry1Constant (r - 1 - 2 * k - 1) a * t ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ) := by
    intro k _
    have hidx : r - 2 * (k + 1) = r - 1 - 2 * k - 1 := by omega
    have hexp : 2 * (k + 1) = 2 * k + 2 := by ring
    have hexp2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
    rw [hidx, hexp]
    have hF1 : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hfact : ((2 * k + 1 + 1).factorial : ℝ) =
        ((2 * k + 1 + 1 : ℕ) : ℝ) * ((2 * k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hfun : (fun t : ℝ => (-1 : ℝ) ^ k *
        chapter9Entry1Constant (r - 1 - 2 * k - 1) a * t ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) =
        (fun t : ℝ => (((-1 : ℝ) ^ k *
          chapter9Entry1Constant (r - 1 - 2 * k - 1) a /
          ((2 * k + 1).factorial : ℝ))) * t ^ (2 * k + 1)) := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul, entry1_integral_pow]
    have hcast : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 1 + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, ← hexp2]
    have hpow : (-1 : ℝ) ^ (k + 1) = -(-1 : ℝ) ^ k := by
      rw [pow_succ]; ring
    rw [hpow]
    have hfact2 : ((2 * k + 2).factorial : ℝ) =
        ((2 * k + 1 + 1 : ℕ) : ℝ) * ((2 * k + 1).factorial : ℝ) := by
      have heq : 2 * k + 2 = 2 * k + 1 + 1 := by omega
      rw [heq]
      exact hfact
    rw [hfact2]
    field_simp
  rw [Finset.sum_congr rfl hper, Finset.sum_neg_distrib]
  ring

theorem entry1_oddLimit_one (a x : ℝ) :
    entry1_oddLimit 1 a x = chapter9Entry1Constant 1 a := by
  unfold entry1_oddLimit
  have hrange : (1 - 1) / 2 + 1 = 1 := rfl
  rw [hrange, Finset.sum_range_one]
  simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one, one_mul, div_one]

theorem entry1_uniform_one (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (B : ℝ)
    (hB0 : 0 ≤ B) (hBpi : B < Real.pi) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1CosineTerm 1 a v k -
        entry1_oddLimit 1 a v| ≤ ε := by
  have hsum : Summable (chapter9Entry1ConstantTerm 1 a) :=
    entry1_const_summable 1 a (by norm_num)
  have hC : Tendsto (fun N => ∑ k ∈ range N,
      chapter9Entry1ConstantTerm 1 a k) atTop
      (𝓝 (chapter9Entry1Constant 1 a)) :=
    hsum.tendsto_sum_tsum_nat
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hC) (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := entry1_rl_nonneg a B hB0 hBpi (ε / 2) hε2
  refine ⟨max N1 N2, fun N hN v hv => ?_⟩
  have hN1' : N ≥ N1 := le_trans (le_max_left _ _) hN
  have hN2' : N ≥ N2 := le_trans (le_max_right _ _) hN
  have hdist := hN1 N hN1'
  rw [dist_eq_norm] at hdist
  rw [Real.norm_eq_abs] at hdist
  have htail : |∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k -
      chapter9Entry1Constant 1 a| ≤ ε / 2 := le_of_lt hdist
  have hrem := hN2 N hN2' v hv
  have hv0 : 0 ≤ v := (Set.mem_Icc.mp hv).1
  have hvB : v ≤ B := (Set.mem_Icc.mp hv).2
  have hvpi : |v| < Real.pi := by
    rw [abs_of_nonneg hv0]
    linarith
  have hbase := entry1_base_identity N a v ha hvpi
  have hlim : entry1_oddLimit 1 a v = chapter9Entry1Constant 1 a :=
    entry1_oddLimit_one a v
  rw [hlim]
  have heq : (∑ k ∈ range N, chapter9Entry1CosineTerm 1 a v k) -
      chapter9Entry1Constant 1 a =
      ((∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k) -
        chapter9Entry1Constant 1 a) +
      (∫ s in (0 : ℝ)..v, (entry1_g a s) * Real.sin (2 * N * s)) := by
    linarith [hbase]
  rw [heq]
  calc |((∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k) -
        chapter9Entry1Constant 1 a) +
        (∫ s in (0 : ℝ)..v, (entry1_g a s) * Real.sin (2 * N * s))|
      ≤ |∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k -
          chapter9Entry1Constant 1 a| +
          |∫ s in (0 : ℝ)..v, (entry1_g a s) * Real.sin (2 * N * s)| :=
        abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add htail hrem
    _ = ε := by ring

theorem entry1_integral_error_bound (f g : ℝ → ℝ) (B v ε' : ℝ)
    (hB0 : 0 ≤ B) (hv : v ∈ Set.Icc 0 B)
    (hbound : ∀ t ∈ Set.Icc 0 B, |f t - g t| ≤ ε') :
    |∫ t in (0 : ℝ)..v, (f t - g t)| ≤ B * ε' := by
  have hv0 : 0 ≤ v := (Set.mem_Icc.mp hv).1
  have hvB : v ≤ B := (Set.mem_Icc.mp hv).2
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 B := ⟨le_rfl, hB0⟩
  have hεnn : 0 ≤ ε' := le_trans (abs_nonneg _) (hbound 0 h0mem)
  have hpt : ∀ s ∈ Set.uIoc 0 v, ‖f s - g s‖ ≤ ε' := by
    intro s hs
    rw [Set.uIoc_of_le hv0, Set.mem_Ioc] at hs
    have hsIcc : s ∈ Set.Icc 0 B := ⟨le_of_lt hs.1, le_trans hs.2 hvB⟩
    rw [Real.norm_eq_abs]
    exact hbound s hsIcc
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs] at hnorm
  have hvabs : |v - 0| = v := by rw [sub_zero, abs_of_nonneg hv0]
  rw [hvabs] at hnorm
  calc |∫ t in (0 : ℝ)..v, (f t - g t)| ≤ ε' * v := hnorm
    _ ≤ ε' * B := mul_le_mul_of_nonneg_left hvB hεnn
    _ = B * ε' := by ring

theorem entry1_step_odd_to_even (s : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (B : ℝ)
    (hB0 : 0 ≤ B) (hBpi : B < Real.pi) (ε : ℝ) (hε : 0 < ε)
    (hs1 : 1 ≤ s)
    (ih : ∀ ε' : ℝ, 0 < ε' → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ v ∈ Set.Icc 0 B,
        |∑ k ∈ range N, chapter9Entry1CosineTerm s a v k -
          entry1_oddLimit s a v| ≤ ε') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1SineTerm (s + 1) a v k -
        entry1_evenLimit (s + 1) a v| ≤ ε := by
  by_cases hB : B = 0
  · subst hB
    refine ⟨0, fun N _ v hv => ?_⟩
    have hv0 : v = 0 := le_antisymm (Set.mem_Icc.mp hv).2 (Set.mem_Icc.mp hv).1
    subst hv0
    have hsum_eq := entry1_sum_sine_eq s N a 0 ha
    have hlim_eq := entry1_evenLimit_eq_integral (s + 1) a 0 (by omega)
    rw [hsum_eq, hlim_eq, intervalIntegral.integral_same,
      intervalIntegral.integral_same, sub_self, abs_zero]
    exact hε.le
  · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
    have hεB : 0 < ε / B := div_pos hε hBpos
    obtain ⟨N0, hN0⟩ := ih (ε / B) hεB
    refine ⟨N0, fun N hN v hv => ?_⟩
    have hsum_eq := entry1_sum_sine_eq s N a v ha
    have hlim_eq := entry1_evenLimit_eq_integral (s + 1) a v (by omega)
    have hr_sub : (s + 1) - 1 = s := by omega
    rw [hr_sub] at hlim_eq
    have hcont_f : Continuous (fun t : ℝ => ∑ k ∈ range N,
        chapter9Entry1CosineTerm s a t k) := by
      apply continuous_finsetSum
      intro k _
      exact entry1_cosTerm_continuous s a k ha
    have hint_f : IntervalIntegrable (fun t : ℝ => ∑ k ∈ range N,
        chapter9Entry1CosineTerm s a t k) volume 0 v :=
      hcont_f.intervalIntegrable 0 v
    have hint_g : IntervalIntegrable (fun t : ℝ =>
        entry1_oddLimit s a t) volume 0 v :=
      (entry1_oddLimit_continuous s a).intervalIntegrable 0 v
    have hsub : (∫ t in (0 : ℝ)..v, ∑ k ∈ range N,
          chapter9Entry1CosineTerm s a t k) -
          (∫ t in (0 : ℝ)..v, entry1_oddLimit s a t) =
          ∫ t in (0 : ℝ)..v, ((∑ k ∈ range N,
            chapter9Entry1CosineTerm s a t k) - entry1_oddLimit s a t) :=
      (intervalIntegral.integral_sub hint_f hint_g).symm
    have heq : (∑ k ∈ range N, chapter9Entry1SineTerm (s + 1) a v k) -
        entry1_evenLimit (s + 1) a v =
        ∫ t in (0 : ℝ)..v, ((∑ k ∈ range N,
          chapter9Entry1CosineTerm s a t k) - entry1_oddLimit s a t) := by
      rw [hsum_eq, hlim_eq, hsub]
    rw [heq]
    have hbound := entry1_integral_error_bound _ _ B v (ε / B) hB0 hv
      (fun t ht => hN0 N hN t ht)
    have hBeq : B * (ε / B) = ε := by field_simp
    rwa [hBeq] at hbound

theorem entry1_step_even_to_odd (s : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (B : ℝ)
    (hB0 : 0 ≤ B) (hBpi : B < Real.pi) (ε : ℝ) (hε : 0 < ε)
    (hs1 : 1 ≤ s)
    (ih : ∀ ε' : ℝ, 0 < ε' → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ v ∈ Set.Icc 0 B,
        |∑ k ∈ range N, chapter9Entry1SineTerm s a v k -
          entry1_evenLimit s a v| ≤ ε') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1CosineTerm (s + 1) a v k -
        entry1_oddLimit (s + 1) a v| ≤ ε := by
  have hsumR : Summable (chapter9Entry1ConstantTerm (s + 1) a) :=
    entry1_const_summable (s + 1) a (by omega)
  have hCR : Tendsto (fun N => ∑ k ∈ range N,
      chapter9Entry1ConstantTerm (s + 1) a k) atTop
      (𝓝 (chapter9Entry1Constant (s + 1) a)) :=
    hsumR.tendsto_sum_tsum_nat
  by_cases hB : B = 0
  · subst hB
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hCR) ε hε
    refine ⟨N1, fun N hN v hv => ?_⟩
    have hdist := hN1 N hN
    rw [dist_eq_norm, Real.norm_eq_abs] at hdist
    have htail : |∑ k ∈ range N,
        chapter9Entry1ConstantTerm (s + 1) a k -
        chapter9Entry1Constant (s + 1) a| ≤ ε := le_of_lt hdist
    have hv0 : v = 0 := le_antisymm (Set.mem_Icc.mp hv).2 (Set.mem_Icc.mp hv).1
    subst hv0
    have hsum_eq := entry1_sum_cosine_eq s N a 0 ha
    have hlim_eq := entry1_oddLimit_eq (s + 1) a 0
    rw [hsum_eq, hlim_eq, intervalIntegral.integral_same,
      intervalIntegral.integral_same]
    simp only [sub_zero]
    exact htail
  · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    have hε2B : (0 : ℝ) < (ε / 2) / B := div_pos hε2 hBpos
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hCR) (ε / 2) hε2
    obtain ⟨N2, hN2⟩ := ih ((ε / 2) / B) hε2B
    refine ⟨max N1 N2, fun N hN v hv => ?_⟩
    have hN1' : N ≥ N1 := le_trans (le_max_left _ _) hN
    have hN2' : N ≥ N2 := le_trans (le_max_right _ _) hN
    have hdist := hN1 N hN1'
    rw [dist_eq_norm, Real.norm_eq_abs] at hdist
    have htail : |∑ k ∈ range N,
        chapter9Entry1ConstantTerm (s + 1) a k -
        chapter9Entry1Constant (s + 1) a| ≤ ε / 2 := le_of_lt hdist
    have hsum_eq := entry1_sum_cosine_eq s N a v ha
    have hlim_eq := entry1_oddLimit_eq (s + 1) a v
    have hr_sub : (s + 1) - 1 = s := by omega
    rw [hr_sub] at hlim_eq
    have hcont_f : Continuous (fun t : ℝ => ∑ k ∈ range N,
        chapter9Entry1SineTerm s a t k) := by
      apply continuous_finsetSum
      intro k _
      exact entry1_sinTerm_continuous s a k ha
    have hint_f : IntervalIntegrable (fun t : ℝ => ∑ k ∈ range N,
        chapter9Entry1SineTerm s a t k) volume 0 v :=
      hcont_f.intervalIntegrable 0 v
    have hint_g : IntervalIntegrable (fun t : ℝ =>
        entry1_evenLimit s a t) volume 0 v :=
      (entry1_evenLimit_continuous s a).intervalIntegrable 0 v
    have hsub : (∫ t in (0 : ℝ)..v, ∑ k ∈ range N,
          chapter9Entry1SineTerm s a t k) -
          (∫ t in (0 : ℝ)..v, entry1_evenLimit s a t) =
          ∫ t in (0 : ℝ)..v, ((∑ k ∈ range N,
            chapter9Entry1SineTerm s a t k) - entry1_evenLimit s a t) :=
      (intervalIntegral.integral_sub hint_f hint_g).symm
    have heq : (∑ k ∈ range N, chapter9Entry1CosineTerm (s + 1) a v k) -
        entry1_oddLimit (s + 1) a v =
        ((∑ k ∈ range N, chapter9Entry1ConstantTerm (s + 1) a k) -
          chapter9Entry1Constant (s + 1) a) -
        ∫ t in (0 : ℝ)..v, ((∑ k ∈ range N,
          chapter9Entry1SineTerm s a t k) - entry1_evenLimit s a t) := by
      rw [hsum_eq, hlim_eq]
      linear_combination -hsub
    rw [heq]
    have hbound := entry1_integral_error_bound _ _ B v ((ε / 2) / B) hB0 hv
      (fun t ht => hN2 N hN2' t ht)
    have hBeq : B * ((ε / 2) / B) = ε / 2 := by field_simp
    rw [hBeq] at hbound
    calc |((∑ k ∈ range N, chapter9Entry1ConstantTerm (s + 1) a k) -
          chapter9Entry1Constant (s + 1) a) -
          ∫ t in (0 : ℝ)..v, ((∑ k ∈ range N,
            chapter9Entry1SineTerm s a t k) - entry1_evenLimit s a t)|
        ≤ |∑ k ∈ range N, chapter9Entry1ConstantTerm (s + 1) a k -
            chapter9Entry1Constant (s + 1) a| +
            |∫ t in (0 : ℝ)..v, ((∑ k ∈ range N,
              chapter9Entry1SineTerm s a t k) - entry1_evenLimit s a t)| :=
          entry1_abs_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add htail hbound
      _ = ε := by ring

theorem entry1_uniform_succ (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (n : ℕ) (B : ℝ)
    (hB0 : 0 ≤ B) (hBpi : B < Real.pi) (ε : ℝ) (hε : 0 < ε) :
    ((Odd (n + 1) → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1CosineTerm (n + 1) a v k -
        entry1_oddLimit (n + 1) a v| ≤ ε) ∧
     (Even (n + 1) → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1SineTerm (n + 1) a v k -
        entry1_evenLimit (n + 1) a v| ≤ ε)) := by
  induction n generalizing B ε with
  | zero =>
    constructor
    · intro _
      exact entry1_uniform_one a ha B hB0 hBpi ε hε
    · intro hEven
      have hEven' : (0 + 1) % 2 = 0 := Nat.even_iff.mp hEven
      have hFalse : False := by omega
      exact False.elim hFalse
  | succ n ih =>
    constructor
    · intro hOdd
      have hOdd' : (n + 1 + 1) % 2 = 1 := Nat.odd_iff.mp hOdd
      have hEvenPrev : Even (n + 1) := by
        rw [Nat.even_iff]
        omega
      have ih_even : ∀ ε' : ℝ, 0 < ε' → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          ∀ v ∈ Set.Icc 0 B,
            |∑ k ∈ range N, chapter9Entry1SineTerm (n + 1) a v k -
              entry1_evenLimit (n + 1) a v| ≤ ε' := by
        intro ε' hε'
        exact (ih B hB0 hBpi ε' hε').2 hEvenPrev
      have hstep := entry1_step_even_to_odd (n + 1) a ha B hB0 hBpi ε hε
        (by omega) ih_even
      have heq : n + 1 + 1 = n + 1 + 1 := rfl
      exact hstep
    · intro hEven
      have hEven' : (n + 1 + 1) % 2 = 0 := Nat.even_iff.mp hEven
      have hOddPrev : Odd (n + 1) := by
        rw [Nat.odd_iff]
        omega
      have ih_odd : ∀ ε' : ℝ, 0 < ε' → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          ∀ v ∈ Set.Icc 0 B,
            |∑ k ∈ range N, chapter9Entry1CosineTerm (n + 1) a v k -
              entry1_oddLimit (n + 1) a v| ≤ ε' := by
        intro ε' hε'
        exact (ih B hB0 hBpi ε' hε').1 hOddPrev
      exact entry1_step_odd_to_even (n + 1) a ha B hB0 hBpi ε hε
        (by omega) ih_odd

theorem entry1_uniform_all (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (B : ℝ) (hB0 : 0 ≤ B) (hBpi : B < Real.pi) (ε : ℝ) (hε : 0 < ε) :
    ((Odd r → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1CosineTerm r a v k -
        entry1_oddLimit r a v| ≤ ε) ∧
     (Even r → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∑ k ∈ range N, chapter9Entry1SineTerm r a v k -
        entry1_evenLimit r a v| ≤ ε)) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  subst hn
  exact entry1_uniform_succ a ha n B hB0 hBpi ε hε

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9,
Entry 1, pp. 233–235.

Proves `Wanted` entry `ramanujan_part1_ch9_entry1_logratio`.
-/
theorem ramanujan_part1_ch9_entry1_logratio (r : ℕ) (a x : ℝ)
    (hr : 0 < r)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (hx : |x| < Real.pi) :
    Summable (chapter9Entry1ConstantTerm r a) ∧
      ((Odd r ∧
          (∀ k ∈ range ((r - 1) / 2 + 1),
            Summable (chapter9Entry1ConstantTerm (r - 2 * k) a)) ∧
          Tendsto
            (fun N : ℕ =>
              ∑ k ∈ range N, chapter9Entry1CosineTerm r a x k)
            atTop
            (𝓝 (∑ k ∈ range ((r - 1) / 2 + 1),
              (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 2 * k) a *
                x ^ (2 * k) / ((2 * k).factorial : ℝ)))) ∨
        (Even r ∧
          (∀ k ∈ range (r / 2),
            Summable (chapter9Entry1ConstantTerm (r - 2 * k - 1) a)) ∧
          Tendsto
            (fun N : ℕ =>
              ∑ k ∈ range N, chapter9Entry1SineTerm r a x k)
            atTop
            (𝓝 (∑ k ∈ range (r / 2),
              (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 2 * k - 1) a *
                x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))))) := by
  have hr1 : 1 ≤ r := by omega
  have hSumm : Summable (chapter9Entry1ConstantTerm r a) :=
    entry1_const_summable r a hr1
  by_cases hmod : r % 2 = 0
  · have hrEven : Even r := Nat.even_iff.mpr hmod
    refine ⟨hSumm, Or.inr ⟨hrEven, ?_, ?_⟩⟩
    · intro k hk
      rw [Finset.mem_range] at hk
      obtain ⟨m, hm⟩ := hrEven
      have h1 : 1 ≤ r - 2 * k - 1 := by omega
      exact entry1_const_summable _ a h1
    · change Tendsto (fun N : ℕ => ∑ k ∈ range N, chapter9Entry1SineTerm r a x k)
          atTop (𝓝 (entry1_evenLimit r a x))
      have hB0 : 0 ≤ |x| := abs_nonneg x
      have hBpi : |x| < Real.pi := hx
      have hsin_neg : ∀ v : ℝ, ∀ k : ℕ,
          chapter9Entry1SineTerm r a (-v) k =
            -chapter9Entry1SineTerm r a v k := by
        intro v k
        unfold chapter9Entry1SineTerm
        have e1 : ((((2 * k + 1 : ℕ) : ℝ) - a) * (-v)) =
            -((((2 * k + 1 : ℕ) : ℝ) - a) * v) := by ring
        have e2 : ((((2 * k + 1 : ℕ) : ℝ) + a) * (-v)) =
            -((((2 * k + 1 : ℕ) : ℝ) + a) * v) := by ring
        rw [e1, e2, Real.sin_neg, Real.sin_neg]
        ring
      have hlim_neg : ∀ v : ℝ,
          entry1_evenLimit r a (-v) = -entry1_evenLimit r a v := by
        intro v
        unfold entry1_evenLimit
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        have hsq : (-v) ^ 2 = v ^ 2 := by ring
        have hpow2 : (-v) ^ (2 * k) = v ^ (2 * k) := by
          rw [pow_mul, pow_mul, hsq]
        have hpow : (-v) ^ (2 * k + 1) = -(v ^ (2 * k + 1)) := by
          rw [pow_succ, pow_succ, hpow2]
          ring
        rw [hpow]
        ring
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hε2 : 0 < ε / 2 := by linarith
      obtain ⟨-, hUeven⟩ :=
        entry1_uniform_all a ha r hr1 |x| hB0 hBpi (ε / 2) hε2
      obtain ⟨N0, hN0⟩ := hUeven hrEven
      refine ⟨N0, fun N hN => ?_⟩
      have hmem : |x| ∈ Set.Icc 0 |x| := ⟨abs_nonneg _, le_rfl⟩
      have hbound := hN0 N hN |x| hmem
      rw [dist_eq_norm, Real.norm_eq_abs]
      by_cases hx0 : 0 ≤ x
      · have hxAbs : |x| = x := abs_of_nonneg hx0
        rw [← hxAbs]
        exact lt_of_le_of_lt hbound (by linarith)
      · have habs : |x| = -x := abs_of_neg (not_le.mp hx0)
        have hxNeg : x = -|x| := by rw [habs, neg_neg]
        rw [hxNeg]
        have hsum_eq : (∑ k ∈ range N, chapter9Entry1SineTerm r a (-|x|) k) =
            -(∑ k ∈ range N, chapter9Entry1SineTerm r a |x| k) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun k _ => hsin_neg _ k)
        rw [hsum_eq, hlim_neg]
        have heq : (-(∑ k ∈ range N, chapter9Entry1SineTerm r a |x| k) -
            -(entry1_evenLimit r a |x|)) =
            -((∑ k ∈ range N, chapter9Entry1SineTerm r a |x| k) -
              entry1_evenLimit r a |x|) := by ring
        rw [heq, abs_neg]
        exact lt_of_le_of_lt hbound (by linarith)
  · have hmod1 : r % 2 = 1 := by omega
    have hrOdd : Odd r := Nat.odd_iff.mpr hmod1
    refine ⟨hSumm, Or.inl ⟨hrOdd, ?_, ?_⟩⟩
    · intro k hk
      rw [Finset.mem_range] at hk
      obtain ⟨m, hm⟩ := hrOdd
      have h1 : 1 ≤ r - 2 * k := by omega
      exact entry1_const_summable _ a h1
    · change Tendsto (fun N : ℕ => ∑ k ∈ range N, chapter9Entry1CosineTerm r a x k)
          atTop (𝓝 (entry1_oddLimit r a x))
      have hB0 : 0 ≤ |x| := abs_nonneg x
      have hBpi : |x| < Real.pi := hx
      have hcos_neg : ∀ v : ℝ, ∀ k : ℕ,
          chapter9Entry1CosineTerm r a (-v) k =
            chapter9Entry1CosineTerm r a v k := by
        intro v k
        unfold chapter9Entry1CosineTerm
        have e1 : ((((2 * k + 1 : ℕ) : ℝ) - a) * (-v)) =
            -((((2 * k + 1 : ℕ) : ℝ) - a) * v) := by ring
        have e2 : ((((2 * k + 1 : ℕ) : ℝ) + a) * (-v)) =
            -((((2 * k + 1 : ℕ) : ℝ) + a) * v) := by ring
        rw [e1, e2, Real.cos_neg, Real.cos_neg]
      have hlim_neg : ∀ v : ℝ,
          entry1_oddLimit r a (-v) = entry1_oddLimit r a v := by
        intro v
        unfold entry1_oddLimit
        apply Finset.sum_congr rfl
        intro k _
        have hsq : (-v) ^ 2 = v ^ 2 := by ring
        have hpow : (-v) ^ (2 * k) = v ^ (2 * k) := by
          rw [pow_mul, pow_mul, hsq]
        rw [hpow]
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hε2 : 0 < ε / 2 := by linarith
      obtain ⟨hUodd, -⟩ :=
        entry1_uniform_all a ha r hr1 |x| hB0 hBpi (ε / 2) hε2
      obtain ⟨N0, hN0⟩ := hUodd hrOdd
      refine ⟨N0, fun N hN => ?_⟩
      have hmem : |x| ∈ Set.Icc 0 |x| := ⟨abs_nonneg _, le_rfl⟩
      have hbound := hN0 N hN |x| hmem
      rw [dist_eq_norm, Real.norm_eq_abs]
      by_cases hx0 : 0 ≤ x
      · have hxAbs : |x| = x := abs_of_nonneg hx0
        rw [← hxAbs]
        exact lt_of_le_of_lt hbound (by linarith)
      · have habs : |x| = -x := abs_of_neg (not_le.mp hx0)
        have hxNeg : x = -|x| := by rw [habs, neg_neg]
        rw [hxNeg]
        have hsum_eq : (∑ k ∈ range N, chapter9Entry1CosineTerm r a (-|x|) k) =
            ∑ k ∈ range N, chapter9Entry1CosineTerm r a |x| k :=
          Finset.sum_congr rfl (fun k _ => hcos_neg _ k)
        rw [hsum_eq, hlim_neg]
        exact lt_of_le_of_lt hbound (by linarith)

end
end Entry1Logratio
end Ramanujan.Part1Ch9
end
