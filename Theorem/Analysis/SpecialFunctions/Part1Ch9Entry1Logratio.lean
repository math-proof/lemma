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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry1Logratio
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

theorem entry1_sub_ne_zero (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (k : ℕ) :
    ((2 * k + 1 : ℕ) : ℝ) - a ≠ 0 := by
  intro h
  have h' : a = ((2 * k + 1 : ℕ) : ℝ) := by linarith
  apply ha (k : ℤ)
  rw [h']
  push_cast
  ring

theorem entry1_add_ne_zero (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (k : ℕ) :
    ((2 * k + 1 : ℕ) : ℝ) + a ≠ 0 := by
  intro h
  have h' : a = -((2 * k + 1 : ℕ) : ℝ) := by linarith
  apply ha (-(k : ℤ) - 1)
  rw [h']
  push_cast
  ring

theorem entry1_aux_summable :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr h
  have hcongr : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext k
    rw [Nat.cast_add, Nat.cast_one]
  rwa [hcongr]

theorem entry1_const_term_norm_le (s : ℕ) (a : ℝ) (hs : 1 ≤ s) (K : ℕ)
    (hK : |a| + 1 < (K : ℝ)) (j : ℕ) :
    ‖chapter9Entry1ConstantTerm s a (j + K)‖ ≤
      (2 * |a| * (s : ℝ) * ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s) /
        (((j : ℝ) + 1) ^ 2) := by
  set y : ℝ := ((2 * (j + K) + 1 : ℕ) : ℝ) with hy
  have hKn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have han : (0 : ℝ) ≤ |a| := abs_nonneg _
  have hcast : y = 2 * (j : ℝ) + 2 * (K : ℝ) + 1 := by
    rw [hy]
    push_cast
    ring
  have hjK1 : ((j : ℝ) + 1) ≤ y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hy2 : 2 * |a| < y := by
    have h2K : 2 * (K : ℝ) + 1 ≤ y := by linarith
    linarith
  have hapos : 0 < y - a := by
    have h1 : a ≤ |a| := le_abs_self a
    linarith
  have hbpos : 0 < y + a := by
    have h1 : -|a| ≤ a := neg_abs_le a
    linarith
  have habs : |a| < y / 2 := by linarith
  have hnum : |(y + a) ^ s - (y - a) ^ s| ≤
      2 * |a| * (s : ℝ) * (y + |a|) ^ (s - 1) := by
    have h := abs_pow_sub_pow_le (a := y + a) (b := y - a) (n := s)
    have hsub : |(y + a) - (y - a)| = 2 * |a| := by
      have : (y + a) - (y - a) = 2 * a := by ring
      rw [this, abs_mul]
      norm_num
    have hmax : max |y + a| |y - a| ≤ y + |a| := by
      rw [abs_of_pos hbpos, abs_of_pos hapos]
      apply max_le _ _
      · linarith [le_abs_self a]
      · linarith [neg_abs_le a]
    have hpow : max |y + a| |y - a| ^ (s - 1) ≤ (y + |a|) ^ (s - 1) := by
      exact pow_le_pow_left₀ ((abs_nonneg _).trans (le_max_left _ _)) hmax _
    calc |(y + a) ^ s - (y - a) ^ s|
        ≤ |(y + a) - (y - a)| * s * max |y + a| |y - a| ^ (s - 1) := h
      _ = 2 * |a| * (s : ℝ) * max |y + a| |y - a| ^ (s - 1) := by
          rw [hsub]
      _ ≤ 2 * |a| * (s : ℝ) * (y + |a|) ^ (s - 1) := by
          have hnn : (0 : ℝ) ≤ 2 * |a| * (s : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hpow hnn
  have hden : (y ^ 2 / 2) ^ s ≤ (y - a) ^ s * (y + a) ^ s := by
    have hsq : y ^ 2 / 2 ≤ (y - a) * (y + a) := by
      have hsq2 : (y - a) * (y + a) = y ^ 2 - a ^ 2 := by ring
      have ha2 : a ^ 2 ≤ (y / 2) ^ 2 := by
        have h1 : |a| ≤ y / 2 := le_of_lt habs
        have h2 : |a| ^ 2 ≤ (y / 2) ^ 2 :=
          pow_le_pow_left₀ han h1 2
        rwa [sq_abs] at h2
      have hy2nn : (0 : ℝ) ≤ y ^ 2 / 2 := by positivity
      nlinarith
    have hnn : (0 : ℝ) ≤ y ^ 2 / 2 := by positivity
    calc (y ^ 2 / 2) ^ s ≤ ((y - a) * (y + a)) ^ s :=
            pow_le_pow_left₀ hnn hsq s
      _ = (y - a) ^ s * (y + a) ^ s := mul_pow _ _ _
  have hdenpos : 0 < (y - a) ^ s * (y + a) ^ s := by positivity
  have hyproducer : (y : ℝ) + |a| ≤ (3 / 2) * y := by linarith
  have hylt : (y + |a|) ^ (s - 1) ≤ ((3 / 2 : ℝ) ^ (s - 1)) * y ^ (s - 1) := by
    have hya : (0 : ℝ) ≤ y + |a| := by linarith [hy1, abs_nonneg a]
    calc (y + |a|) ^ (s - 1) ≤ ((3 / 2 : ℝ) * y) ^ (s - 1) :=
            pow_le_pow_left₀ hya hyproducer (s - 1)
      _ = ((3 / 2 : ℝ) ^ (s - 1)) * y ^ (s - 1) := mul_pow _ _ _
  have hysub : y ^ (s - 1) ≤ y ^ (2 * s - 2) := by
    apply pow_le_pow_right₀ hy1
    omega
  have h2s : (2 : ℕ) ≤ 2 * s := by omega
  have hppow : y ^ (2 * s - 2) * y ^ 2 = y ^ (2 * s) := by
    have hadd : 2 * s - 2 + 2 = 2 * s := Nat.sub_add_cancel h2s
    conv_rhs => rw [← hadd]
    rw [pow_add]
  have hy2pow : y ^ (2 * s) = (y ^ 2) ^ s := by rw [← pow_mul]
  have hmain : ‖chapter9Entry1ConstantTerm s a (j + K)‖ * (((j : ℝ) + 1) ^ 2) ≤
      2 * |a| * (s : ℝ) * ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s := by
    have hterm : chapter9Entry1ConstantTerm s a (j + K) =
        ((y + a) ^ s - (y - a) ^ s) / ((y - a) ^ s * (y + a) ^ s) := by
      unfold chapter9Entry1ConstantTerm
      rw [hy]
      have h1 : ((2 * (j + K) + 1 : ℕ) : ℝ) = y := rfl
      rw [h1]
      have e1 : (y - a) ^ s ≠ 0 := pow_ne_zero s (ne_of_gt hapos)
      have e2 : (y + a) ^ s ≠ 0 := pow_ne_zero s (ne_of_gt hbpos)
      field_simp
    rw [hterm, Real.norm_eq_abs, abs_div]
    have habsden : |(y - a) ^ s * (y + a) ^ s| = (y - a) ^ s * (y + a) ^ s :=
      abs_of_pos hdenpos
    rw [habsden]
    have hj2 : (((j : ℝ) + 1) ^ 2) ≤ y ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hjK1 2
    have hdiv : |(y + a) ^ s - (y - a) ^ s| / ((y - a) ^ s * (y + a) ^ s) ≤
        (2 * |a| * (s : ℝ) * (y + |a|) ^ (s - 1)) /
          ((y - a) ^ s * (y + a) ^ s) :=
      (div_le_div_iff_of_pos_right hdenpos).mpr hnum
    have hdiv2nn : (0 : ℝ) ≤ (2 * |a| * (s : ℝ) * (y + |a|) ^ (s - 1)) /
        ((y - a) ^ s * (y + a) ^ s) := by
      apply div_nonneg _ hdenpos.le
      have h1 : (0 : ℝ) ≤ 2 * |a| * (s : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (y + |a|) ^ (s - 1) := by
        apply pow_nonneg _ _
        linarith [hy1, abs_nonneg a]
      exact mul_nonneg h1 h2
    have hle1 : |(y + a) ^ s - (y - a) ^ s| / ((y - a) ^ s * (y + a) ^ s) *
        (((j : ℝ) + 1) ^ 2) ≤
        (2 * |a| * (s : ℝ) * (y + |a|) ^ (s - 1)) / ((y - a) ^ s * (y + a) ^ s) *
        (y ^ 2) :=
      mul_le_mul hdiv hj2 (by positivity) hdiv2nn
    have hle2 : (2 * |a| * (s : ℝ) * (y + |a|) ^ (s - 1)) /
          ((y - a) ^ s * (y + a) ^ s) * (y ^ 2) ≤
        2 * |a| * (s : ℝ) * ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s := by
      have hB2 : (y + |a|) ^ (s - 1) ≤
          ((3 / 2 : ℝ) ^ (s - 1)) * y ^ (2 * s - 2) := by
        calc (y + |a|) ^ (s - 1)
            ≤ ((3 / 2 : ℝ) ^ (s - 1)) * y ^ (s - 1) := hylt
          _ ≤ ((3 / 2 : ℝ) ^ (s - 1)) * y ^ (2 * s - 2) :=
              mul_le_mul_of_nonneg_left hysub (by positivity)
      have hD' : y ^ (2 * s) / 2 ^ s ≤ (y - a) ^ s * (y + a) ^ s := by
        have hcancel : (y ^ 2 / 2) ^ s = y ^ (2 * s) / 2 ^ s := by
          rw [div_pow, hy2pow]
        rwa [hcancel] at hden
      have h2sne : (2 : ℝ) ^ s ≠ 0 := by positivity
      have hRed : (y + |a|) ^ (s - 1) * y ^ 2 ≤
          ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s * ((y - a) ^ s * (y + a) ^ s) := by
        calc (y + |a|) ^ (s - 1) * y ^ 2
            ≤ (((3 / 2 : ℝ) ^ (s - 1)) * y ^ (2 * s - 2)) * y ^ 2 :=
              mul_le_mul_of_nonneg_right hB2 (by positivity)
          _ = (3 / 2 : ℝ) ^ (s - 1) * y ^ (2 * s) := by
              rw [mul_assoc, hppow]
          _ = (3 / 2 : ℝ) ^ (s - 1) * (y ^ (2 * s) / 2 ^ s) * 2 ^ s := by
              rw [mul_assoc, div_mul_cancel₀ _ h2sne]
          _ ≤ (3 / 2 : ℝ) ^ (s - 1) * ((y - a) ^ s * (y + a) ^ s) * 2 ^ s := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hD' (by positivity)
          _ = ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s * ((y - a) ^ s * (y + a) ^ s) := by
              ring
      have hfac : (0 : ℝ) ≤ 2 * |a| * (s : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hRed hfac
      rw [div_mul_eq_mul_div, div_le_iff₀ hdenpos]
      ring_nf at hmul ⊢
      linarith [hmul]
    linarith [hle1, hle2]
  have hpos2 : (0 : ℝ) < (((j : ℝ) + 1) ^ 2) := by positivity
  rw [le_div_iff₀ hpos2]
  exact hmain

theorem entry1_const_summable (s : ℕ) (a : ℝ) (hs : 1 ≤ s) :
    Summable (chapter9Entry1ConstantTerm s a) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (|a| + 1)
  rw [← summable_nat_add_iff K]
  have hC : Summable (fun j : ℕ =>
      (2 * |a| * (s : ℝ) * ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s) /
        (((j : ℝ) + 1) ^ 2)) := by
    have hmul := entry1_aux_summable.mul_left
      (2 * |a| * (s : ℝ) * ((3 / 2 : ℝ) ^ (s - 1)) * 2 ^ s)
    refine hmul.congr (fun j => mul_one_div _ _)
  refine Summable.of_norm
    (Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => entry1_const_term_norm_le s a hs K hK j) hC)

theorem entry1_dirichlet (N : ℕ) (s : ℝ) (hs : Real.sin s ≠ 0) :
    ∑ k ∈ range N, Real.cos (((2 * k + 1 : ℕ) : ℝ) * s) =
      Real.sin (2 * (N : ℝ) * s) / (2 * Real.sin s) := by
  have h2 : (2 : ℝ) * Real.sin s ≠ 0 := mul_ne_zero (by norm_num) hs
  rw [eq_div_iff h2, Finset.sum_mul]
  have hterm : ∀ k ∈ range N, Real.cos (((2 * k + 1 : ℕ) : ℝ) * s) *
      (2 * Real.sin s) =
      Real.sin (((2 * (k + 1) : ℕ) : ℝ) * s) -
        Real.sin (((2 * k : ℕ) : ℝ) * s) := by
    intro k _
    have h1 : ((((2 * k + 1 : ℕ) : ℝ) * s) + s) =
        (((2 * (k + 1) : ℕ) : ℝ) * s) := by
      push_cast
      ring
    have h2' : ((((2 * k + 1 : ℕ) : ℝ) * s) - s) =
        (((2 * k : ℕ) : ℝ) * s) := by
      push_cast
      ring
    have e : Real.sin (((((2 * k + 1 : ℕ) : ℝ) * s) + s)) -
        Real.sin (((((2 * k + 1 : ℕ) : ℝ) * s) - s)) =
        Real.cos ((((2 * k + 1 : ℕ) : ℝ) * s)) * (2 * Real.sin s) := by
      rw [Real.sin_add, Real.sin_sub]
      ring
    rw [h1, h2'] at e
    exact e.symm
  have hsum : (∑ k ∈ range N, Real.cos (((2 * k + 1 : ℕ) : ℝ) * s) *
      (2 * Real.sin s)) =
      ∑ k ∈ range N, (Real.sin (((2 * (k + 1) : ℕ) : ℝ) * s) -
        Real.sin (((2 * k : ℕ) : ℝ) * s)) :=
    Finset.sum_congr rfl hterm
  rw [hsum]
  set f : ℕ → ℝ := fun j => Real.sin (((2 * j : ℕ) : ℝ) * s) with hf
  have hrewrite : (∑ k ∈ range N, (Real.sin (((2 * (k + 1) : ℕ) : ℝ) * s) -
      Real.sin (((2 * k : ℕ) : ℝ) * s))) = ∑ k ∈ range N, (f (k + 1) - f k) :=
    rfl
  rw [hrewrite, Finset.sum_range_sub]
  simp only [hf]
  have hN : (((2 * N : ℕ) : ℝ) * s) = 2 * (N : ℝ) * s := by
    push_cast
    ring
  have h0 : (((2 * 0 : ℕ) : ℝ) * s) = 0 := by simp
  rw [hN, h0, Real.sin_zero, sub_zero]

end
end Entry1Logratio
end Ramanujan.Part1Ch9
end
