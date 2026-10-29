import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4AlternatingForm

/--
[ramanujan_part1_ch2_entry4_alternating_form_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4AlternatingForm.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry4_alternating_form_general
  {n : ℕ} :
-- imply
  (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * n), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
-- proof
  have gen : ∀ m : ℕ,
    (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 m, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * m + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * m), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have eA : 4 * (n + 1) + 1 = 4 * n + 5 := by ring
      have eB : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [eA, eB]
      have peelL : (∑ k ∈ Finset.Icc 1 (n + 1), (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))) =
        (∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))) +
        (1 / ((4 * (((n + 1 : ℕ)) : ℝ)) ^ 3 - 4 * (((n + 1 : ℕ)) : ℝ))) :=
        Finset.sum_Icc_succ_top (by omega) _
      have peelA1 : (∑ k ∈ Finset.Icc 1 (4 * n + 5), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (4 * n + 4), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
        ((-1 : ℝ) ^ ((4 * n + 5) + 1) / (((4 * n + 5 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 4) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 4) + 1 = 4 * n + 5 from by ring] at h
      have peelA2 : (∑ k ∈ Finset.Icc 1 (4 * n + 4), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (4 * n + 3), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
        ((-1 : ℝ) ^ ((4 * n + 4) + 1) / (((4 * n + 4 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 3) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 3) + 1 = 4 * n + 4 from by ring] at h
      have peelA3 : (∑ k ∈ Finset.Icc 1 (4 * n + 3), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (4 * n + 2), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
        ((-1 : ℝ) ^ ((4 * n + 3) + 1) / (((4 * n + 3 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 2) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 2) + 1 = 4 * n + 3 from by ring] at h
      have peelA4 : (∑ k ∈ Finset.Icc 1 (4 * n + 2), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
        ((-1 : ℝ) ^ ((4 * n + 2) + 1) / (((4 * n + 2 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 1) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 1) + 1 = 4 * n + 2 from by ring] at h
      have peelB1 : (∑ k ∈ Finset.Icc 1 (2 * n + 2), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (2 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
        ((-1 : ℝ) ^ ((2 * n + 2) + 1) / (((2 * n + 2 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 1) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (2 * n + 1) + 1 = 2 * n + 2 from by ring] at h
      have peelB2 : (∑ k ∈ Finset.Icc 1 (2 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (2 * n + 0), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
        ((-1 : ℝ) ^ ((2 * n + 1) + 1) / (((2 * n + 1 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 0) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (2 * n + 0) + 1 = 2 * n + 1 from by ring] at h
      have hB0 : Finset.Icc 1 (2 * n + 0) = Finset.Icc 1 (2 * n) := by ring_nf
      rw [peelL, peelA1, peelA2, peelA3, peelA4, peelB1, peelB2, hB0]
      have s2 : ((-1 : ℝ) ^ ((4 * n + 2) + 1)) = -1 :=
        ((by rw [Nat.odd_iff]; omega : Odd ((4 * n + 2) + 1))).neg_one_pow
      have s3 : ((-1 : ℝ) ^ ((4 * n + 3) + 1)) = 1 :=
        ((by rw [Nat.even_iff]; omega : Even ((4 * n + 3) + 1))).neg_one_pow
      have s4 : ((-1 : ℝ) ^ ((4 * n + 4) + 1)) = -1 :=
        ((by rw [Nat.odd_iff]; omega : Odd ((4 * n + 4) + 1))).neg_one_pow
      have s5 : ((-1 : ℝ) ^ ((4 * n + 5) + 1)) = 1 :=
        ((by rw [Nat.even_iff]; omega : Even ((4 * n + 5) + 1))).neg_one_pow
      have t1 : ((-1 : ℝ) ^ ((2 * n + 1) + 1)) = 1 :=
        ((by rw [Nat.even_iff]; omega : Even ((2 * n + 1) + 1))).neg_one_pow
      have t2 : ((-1 : ℝ) ^ ((2 * n + 2) + 1)) = -1 :=
        ((by rw [Nat.odd_iff]; omega : Odd ((2 * n + 2) + 1))).neg_one_pow
      rw [s2, s3, s4, s5, t1, t2]
      push_cast
      have key : 2 * (1 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1))) =
        (-1 / (4 * (n : ℝ) + 2) + 1 / (4 * (n : ℝ) + 3) - 1 / (4 * (n : ℝ) + 4) +
        1 / (4 * (n : ℝ) + 5)) +
        (1 / 2 : ℝ) * (1 / (2 * (n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 2)) := by
        have hpos : (0 : ℝ) < (4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1) := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 1),
            mul_nonneg hn hn,
            mul_pos (show (0 : ℝ) < (n : ℝ) + 1 by linarith)
              (show (0 : ℝ) < (n : ℝ) + 1 by linarith)]
        have h1 : (4 * (n : ℝ) + 2) ≠ 0 := by positivity
        have h2 : (4 * (n : ℝ) + 3) ≠ 0 := by positivity
        have h3 : (4 * (n : ℝ) + 4) ≠ 0 := by positivity
        have h4 : (4 * (n : ℝ) + 5) ≠ 0 := by positivity
        have h5 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
        have h6 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
        have h7 : ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) ≠ 0 := ne_of_gt hpos
        have e : 2 * (1 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)))
          = 2 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) := by ring
        rw [e, div_eq_iff h7]
        field_simp
        ring
      linear_combination ih + key
  exact gen n

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4AlternatingForm

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4AlternatingForm

/--
[ramanujan_part1_ch2_entry4_alternating_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4AlternatingForm.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry4_alternating_form
  {n : ℕ}
-- given
  (_hn : 0 < n) :
-- imply
  (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * n), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
-- proof
  apply ramanujan_part1_ch2_entry4_alternating_form_general

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4AlternatingForm


-- created on 2026-10-20
-- updated on 2026-10-28
