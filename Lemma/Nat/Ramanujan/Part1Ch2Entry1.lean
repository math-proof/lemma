import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1

/--
[icc_one_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry1.lean)
-/
@[path]
private lemma icc_one_eq_range (n : ℕ) (h : ℕ → ℝ) :
  ∑ k ∈ Finset.Icc 1 n, h k = ∑ k ∈ Finset.range n, h (k + 1) := by
  have h1 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1

/--
[ramanujan_part1_ch2_entry1_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry1.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry1_general
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
    (n : ℝ) / (2 * (n : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) /
    ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) := by
-- proof
  have aux : ∀ m : ℕ,
    ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((m : ℝ) + (k : ℝ)) =
      (m : ℝ) / (2 * (m : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) /
        ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have hR : ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) =
        (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ))) +
        (1 : ℝ) / ((2 * ((((n + 1 : ℕ)) : ℝ))) ^ 3 - 2 * ((((n + 1 : ℕ)) : ℝ))) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hA1 : ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
        ∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ)) := by
        rw [icc_one_eq_range]
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      have hA2 : ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)) =
        ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ)) := by
        rw [icc_one_eq_range]
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      have hD_top : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ)) =
        (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ))) +
        (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) :=
        Finset.sum_range_succ _ _
      have hD_bot : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ)) =
        (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ))) +
        (1 : ℝ) / ((n : ℝ) + 1) := by
        rw [Finset.sum_range_succ']
        congr 1
        · apply Finset.sum_congr rfl
          intro k _
          congr 1
          push_cast
          ring
        · simp
      have hA2_top : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ)) =
        (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ))) +
        (1 : ℝ) / ((n : ℝ) + 2 + ((n : ℕ) : ℝ)) :=
        Finset.sum_range_succ _ _
      rw [hR, hA2]
      rw [hA1] at ih
      have hDeq : (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ))) +
        (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) =
        (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ))) +
        (1 : ℝ) / ((n : ℝ) + 1) := by
        rw [← hD_top, hD_bot]
      have hLHS : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ)) =
        (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ))) +
        (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) -
        (1 : ℝ) / ((n : ℝ) + 1) +
        (1 : ℝ) / ((n : ℝ) + 2 + ((n : ℕ) : ℝ)) := by
        rw [hA2_top]
        linarith [hDeq]
      rw [hLHS, ih]
      have hn1n : (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) = (1 : ℝ) / (2 * (n : ℝ) + 1) := by
        congr 1
        ring
      have hn2n : (1 : ℝ) / ((n : ℝ) + 2 + ((n : ℕ) : ℝ)) = (1 : ℝ) / (2 * (n : ℝ) + 2) := by
        congr 1
        ring
      rw [hn1n, hn2n]
      have hcast : ((((n + 1 : ℕ)) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hterm : (1 : ℝ) / ((2 * (((n : ℝ) + 1))) ^ 3 - 2 * (((n : ℝ) + 1))) =
        (1 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)) := by
        congr 1
        ring
      rw [hterm]
      have h2n3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      have h2n2' : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
      have h2n1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
  exact aux n
set_option linter.unusedVariables false in

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1

/--
[ramanujan_part1_ch2_entry1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry1.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry1
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
    (n : ℝ) / (2 * (n : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) /
    ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) :=
-- proof
  ramanujan_part1_ch2_entry1_general ..

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1


-- created on 2026-10-20
-- updated on 2026-10-23
