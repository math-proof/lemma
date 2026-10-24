import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7

/--
[ramanujan_part1_ch2_entry7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry7
  {n : ℝ}
  {r : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.range r, Real.arctan (2 / (n + 2 * (k : ℝ) + 1) ^ 2) =
      Real.arctan (2 * (r : ℝ) / (n ^ 2 + 2 * n * (r : ℝ) + 1)) := by
-- proof
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hD : (0 : ℝ) < n ^ 2 + 2 * n * (r : ℝ) + 1 := by positivity
    have hD' : (0 : ℝ) < n ^ 2 + 2 * n * ((r : ℝ) + 1) + 1 := by positivity
    have hE : (0 : ℝ) < n + 2 * (r : ℝ) + 1 := by positivity
    set A : ℝ := 2 * (r : ℝ) / (n ^ 2 + 2 * n * (r : ℝ) + 1) with hA
    set C : ℝ := 2 * ((r : ℝ) + 1) / (n ^ 2 + 2 * n * ((r : ℝ) + 1) + 1) with hC
    set B : ℝ := 2 / (n + 2 * (r : ℝ) + 1) ^ 2 with hB
    have hA_nonneg : 0 ≤ A := by positivity
    have hC_nonneg : 0 ≤ C := by positivity
    have hCA : 0 ≤ C * A := mul_nonneg hC_nonneg hA_nonneg
    have h1CA : (0 : ℝ) < 1 + C * A := by linarith
    have h1CA' : (1 : ℝ) + C * A ≠ 0 := ne_of_gt h1CA
    have hcond : C * (-A) < 1 := by
      have : C * (-A) = -(C * A) := by ring
      rw [this]
      linarith
    have hadd := Real.arctan_add (x := C) (y := -A) hcond
    rw [Real.arctan_neg] at hadd
    have hsub : C + -A = C - A := by ring
    have hden : (1 : ℝ) - C * -A = 1 + C * A := by ring
    rw [hsub, hden] at hadd
    have hEq : (C - A) / (1 + C * A) = B := by
      rw [hA, hC, hB]
      have hDne : (n ^ 2 + 2 * n * (r : ℝ) + 1) ≠ 0 := ne_of_gt hD
      have hDne' : (n ^ 2 + 2 * n * ((r : ℝ) + 1) + 1) ≠ 0 := ne_of_gt hD'
      have hEne : (n + 2 * (r : ℝ) + 1) ≠ 0 := ne_of_gt hE
      have hE2ne : ((n + 2 * (r : ℝ) + 1) ^ 2) ≠ 0 := pow_ne_zero 2 hEne
      field_simp
      ring
    rw [hEq] at hadd
    -- hadd : arctan C + -arctan A = arctan B
    have hgoal : Real.arctan A + Real.arctan B = Real.arctan C := by linarith [hadd]
    -- cast alignment: goal uses ((r+1 : ℕ) : ℝ) forms
    push_cast at hgoal ⊢
    -- hgoal and goal should now match up to the definitions of A B C
    rw [hA, hC, hB] at hgoal
    linarith [hgoal]
    -- NOTE: above linarith needs exact syntactic match; fallback:
    -- exact hgoal

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7


-- created on 2026-10-20
-- updated on 2026-10-23
