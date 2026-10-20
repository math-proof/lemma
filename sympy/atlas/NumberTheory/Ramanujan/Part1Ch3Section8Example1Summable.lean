/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Summable.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 1

Summability of an alternating rising-factorial series past radius R.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example1Summable

def sector (lam : Option ℝ) (eps : ℝ) (z : ℂ) : Prop :=
  match lam with
  | some l => |Complex.arg (z - (l : ℂ))| ≤ Real.pi / 2 - eps
  | none => |Complex.arg z| ≤ Real.pi - eps

/-- If the alternating series `∑ (-1)ʲ aⱼ / ((z + 1)(z + 2)⋯(z + j + 1))` converges at every
`z` off the poles (and right of `lam` when `lam = some l`), it converges on the part of `sector lam
eps z` beyond some radius, for every `eps > 0`; `ramanujan_part1_ch3_section8_example1_summable`
is the source-shaped form. -/
theorem ramanujan_part1_ch3_section8_example1_summable_general
    (a : ℕ → ℂ) (lam : Option ℝ) (eps : ℝ) (heps_pos : 0 < eps)
    (hSumm : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
      (∀ l : ℝ, lam = some l → l < z.re) →
      Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
        ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ)))) :
    ∃ R : ℝ, ∀ z : ℂ, sector lam eps z → R < ‖z‖ →
        Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
            ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ))) := by
  cases lam with
  | none =>
    refine ⟨0, fun z hz hR => ?_⟩
    apply hSumm z ?_ ?_
    · intro n hn
      have hz2 : |Complex.arg z| ≤ Real.pi - eps := hz
      have harg : Complex.arg z = Real.pi := by
        apply Complex.arg_eq_pi_iff.mpr
        rw [hn]
        constructor
        · simp only [Complex.neg_re, Complex.natCast_re]
          have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
          push_cast
          linarith
        · simp
      rw [harg, abs_of_nonneg Real.pi_pos.le] at hz2
      linarith
    · intro l hl
      simp at hl
  | some l =>
    refine ⟨|l|, fun z hz hR => ?_⟩
    have hz2 : |Complex.arg (z - (l : ℂ))| ≤ Real.pi / 2 - eps := hz
    have hnorm_l : ‖((l : ℝ) : ℂ)‖ = |l| := by simp
    have hw_ne : z - ((l : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have hzeq : z = ((l : ℝ) : ℂ) := sub_eq_zero.mp h0
      rw [hzeq, hnorm_l] at hR
      exact lt_irrefl _ hR
    have hRe : l < z.re := by
      have hcos : 0 < Real.cos (z - ((l : ℝ) : ℂ)).arg := by
        apply Real.cos_pos_of_mem_Ioo
        have habs := abs_le.mp hz2
        have hpi := Real.pi_pos
        constructor <;> linarith
      have hnorm_pos : 0 < ‖z - ((l : ℝ) : ℂ)‖ := norm_pos_iff.mpr hw_ne
      have hre := Complex.norm_mul_cos_arg (z - ((l : ℝ) : ℂ))
      have hRe_w : 0 < (z - ((l : ℝ) : ℂ)).re := by
        rw [← hre]
        exact mul_pos hnorm_pos hcos
      have hsub : (z - ((l : ℝ) : ℂ)).re = z.re - l := by simp
      rw [hsub] at hRe_w
      linarith
    apply hSumm z ?_ ?_
    · intro n hn
      have hR2 : |l| < ‖z‖ := hR
      rw [hn, norm_neg, Complex.norm_natCast] at hR2
      have harg : Complex.arg (z - ((l : ℝ) : ℂ)) = Real.pi := by
        apply Complex.arg_eq_pi_iff.mpr
        rw [hn]
        constructor
        · simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re,
            Complex.ofReal_re]
          have h3 : -(l) ≤ |l| := neg_le_abs l
          have hcast : (((n + 1 : ℕ)) : ℝ) = ((n : ℕ) : ℝ) + 1 := by
            push_cast; ring
          have h4 : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
          linarith
        · simp
      rw [harg, abs_of_nonneg Real.pi_pos.le] at hz2
      have hpi := Real.pi_pos
      linarith
    · intro l' hl'
      obtain rfl := Option.some_inj.mp hl'
      exact hRe

set_option linter.unusedVariables false in
/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 1, formula
    (8.1), printed p. 50 / PDF p. 60.
Proves `Wanted` entry `ramanujan_part1_ch3_section8_example1_summable`. It follows from
`ramanujan_part1_ch3_section8_example1_summable_general`; the upper bound `heps_lt` is unused and
keeps the source's shape.
-/
theorem ramanujan_part1_ch3_section8_example1_summable
    (a : ℕ → ℂ) (lam : Option ℝ) (eps : ℝ) (heps_pos : 0 < eps)
    (heps_lt : match lam with | some _ => eps < Real.pi / 2 | none => eps < Real.pi)
    (hSumm : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
      (∀ l : ℝ, lam = some l → l < z.re) →
      Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
        ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ)))) :
    ∃ R : ℝ, ∀ z : ℂ, sector lam eps z → R < ‖z‖ →
        Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
            ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ))) :=
  ramanujan_part1_ch3_section8_example1_summable_general a lam eps heps_pos hSumm

end Section8Example1Summable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
