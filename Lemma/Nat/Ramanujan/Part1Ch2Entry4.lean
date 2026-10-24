import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[S1_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma S1_reindex (n : ℕ) :
  (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
  ∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (j : ℝ) := by
  have himg : Finset.image (fun x => n + x) (Finset.Icc 1 n) = Finset.Icc (n + 1) (2 * n) := by
    have h : n + n = 2 * n := by ring
    rw [Finset.image_add_left_Icc, h]
  have hinj : Function.Injective (fun x => n + x) := by
    intro a b h
    dsimp at h
    omega
  rw [← himg, Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring_nf

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[S2_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma S2_reindex (n : ℕ) :
  (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
  ∑ j ∈ Finset.Icc n (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1) := by
  have himg : Finset.image (fun x => n + x) (Finset.Icc 0 n) = Finset.Icc n (2 * n) := by
    have h1 : n + 0 = n := by ring
    have h2 : n + n = 2 * n := by ring
    rw [Finset.image_add_left_Icc, h1, h2]
  have hinj : Function.Injective (fun x => n + x) := by
    intro a b h
    dsimp at h
    omega
  rw [← himg, Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring_nf

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[S1_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma S1_step (n : ℕ) :
  (∑ j ∈ Finset.Icc (n + 2) (2 * (n + 1)), (1 : ℝ) / (j : ℝ)) -
  (∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (j : ℝ)) =
  1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 2) - 1 / ((n : ℝ) + 1) := by
  obtain rfl | hpos := Nat.eq_zero_or_pos n
  · simp
  · have h1 : n + 2 ≤ 2 * n + 1 + 1 := by omega
    have h2 : n + 2 ≤ 2 * n + 1 := by omega
    have h3 : n + 1 ≤ 2 * n := by omega
    have htop1 : ∑ j ∈ Finset.Icc (n + 2) (2 * (n + 1)), (1 : ℝ) / (j : ℝ)
      = (∑ j ∈ Finset.Icc (n + 2) (2 * n + 1), (1 : ℝ) / (j : ℝ))
        + 1 / ((2 * (n + 1) : ℕ) : ℝ) := by
      have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h1 _
    have htop2 : ∑ j ∈ Finset.Icc (n + 2) (2 * n + 1), (1 : ℝ) / (j : ℝ)
      = (∑ j ∈ Finset.Icc (n + 2) (2 * n), (1 : ℝ) / (j : ℝ)) + 1 / ((2 * n + 1 : ℕ) : ℝ) := by
      have h : 2 * n + 1 = (2 * n) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h2 _
    have hbot : ∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (j : ℝ)
      = 1 / (((n + 1 : ℕ)) : ℝ) + ∑ j ∈ Finset.Icc (n + 2) (2 * n), (1 : ℝ) / (j : ℝ) := by
      have hIcc : Finset.Icc (n + 1) (2 * n) = insert (n + 1) (Finset.Icc (n + 2) (2 * n)) := by
        have h : n + 1 + 1 = n + 2 := by omega
        rw [← h]
        exact (Finset.insert_Icc_add_one_left_eq_Icc h3).symm
      rw [hIcc, Finset.sum_insert (by simp)]
    rw [htop1, htop2, hbot]
    push_cast
    ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[S2_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma S2_step (n : ℕ) :
  (∑ j ∈ Finset.Icc (n + 1) (2 * (n + 1)), (1 : ℝ) / (2 * (j : ℝ) + 1)) -
  (∑ j ∈ Finset.Icc n (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1)) =
  1 / (4 * (n : ℝ) + 3) + 1 / (4 * (n : ℝ) + 5) - 1 / (2 * (n : ℝ) + 1) := by
  obtain rfl | hpos := Nat.eq_zero_or_pos n
  · have e1 : Finset.Icc (0 + 1) (2 * (0 + 1)) = ({1, 2} : Finset ℕ) := by decide
    have e2 : Finset.Icc (0 : ℕ) (2 * 0) = ({0} : Finset ℕ) := by decide
    rw [e1, e2]
    norm_num
  · have h1 : n + 1 ≤ 2 * n + 1 + 1 := by omega
    have h2 : n + 1 ≤ 2 * n + 1 := by omega
    have h3 : n ≤ 2 * n := by omega
    have htop1 : ∑ j ∈ Finset.Icc (n + 1) (2 * (n + 1)), (1 : ℝ) / (2 * (j : ℝ) + 1)
      = (∑ j ∈ Finset.Icc (n + 1) (2 * n + 1), (1 : ℝ) / (2 * (j : ℝ) + 1))
        + 1 / (2 * ((2 * (n + 1) : ℕ) : ℝ) + 1) := by
      have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h1 _
    have htop2 : ∑ j ∈ Finset.Icc (n + 1) (2 * n + 1), (1 : ℝ) / (2 * (j : ℝ) + 1)
      = (∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1))
        + 1 / (2 * ((2 * n + 1 : ℕ) : ℝ) + 1) := by
      have h : 2 * n + 1 = (2 * n) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h2 _
    have hbot : ∑ j ∈ Finset.Icc n (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1)
      = 1 / (2 * ((n : ℕ) : ℝ) + 1)
        + ∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1) := by
      have hIcc : Finset.Icc n (2 * n) = insert n (Finset.Icc (n + 1) (2 * n)) := by
        exact (Finset.insert_Icc_add_one_left_eq_Icc h3).symm
      rw [hIcc, Finset.sum_insert (by simp)]
    rw [htop1, htop2, hbot]
    push_cast
    ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[key_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma key_id (n : ℕ) :
  (1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 2) - 1 / ((n : ℝ) + 1) +
  (1 / (4 * (n : ℝ) + 3) + 1 / (4 * (n : ℝ) + 5) - 1 / (2 * (n : ℝ) + 1))) =
  2 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) := by
  have h2 : (2 : ℝ) * (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h4 : (4 : ℝ) * (n : ℝ) + 3 ≠ 0 := by positivity
  have h5 : (4 : ℝ) * (n : ℝ) + 5 ≠ 0 := by positivity
  have h41 : (4 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  have h_factor : (4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)
    = 4 * ((n : ℝ) + 1) * (4 * (n : ℝ) + 3) * (4 * (n : ℝ) + 5) := by ring
  rw [h_factor]
  field_simp
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[ramanujan_part1_ch2_entry4_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry4_general
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) + (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) /
    (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
    1 + 2 * (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    have hL1n := S1_reindex n
    have hL1s := S1_reindex (n + 1)
    have hL2n := S2_reindex n
    have hL2s := S2_reindex (n + 1)
    have st1 := S1_step n
    have st2 := S2_step n
    have kk := key_id n
    have hrhs : (∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))
      = (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))
        + 1 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) := by
      have h := Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ n + 1 by omega)
        (fun k => (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))
      rw [h]
      congr 1
      push_cast
      ring_nf
    have e1 : n + 1 + 1 = n + 2 := by omega
    rw [e1] at hL1s
    linear_combination ih + hL1s - hL1n + hL2s - hL2n + st1 + st2 + kk - 2 * hrhs
set_option linter.unusedVariables false in

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4

/--
[ramanujan_part1_ch2_entry4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry4
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) + (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) /
    (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
    1 + 2 * (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) := by
-- proof
  exact ramanujan_part1_ch2_entry4_general n

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4


-- created on 2026-10-20
-- updated on 2026-10-23
