/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Farey.lean -/


import Def.NumberTheory.Farey
import Lemma.Nat.Farey
import Mathlib.Tactic
open Farey


example : (0 : ℚ) ∈ fareySeq 1 ∧ (1 : ℚ) ∈ fareySeq 1 := by
  constructor <;> rw [mem_fareySeq_iff, mem_fareyFinset_iff] <;> norm_num

example : (1 / 2 : ℚ) ∈ fareySeq 2 := by
  rw [mem_fareySeq_iff, mem_fareyFinset_iff]
  norm_num

example : (fareySeq 4).SortedLT := fareySeq_sorted 4

example : (1 / 5 : ℚ) ∉ fareySeq 4 := by
  rw [mem_fareySeq_iff, mem_fareyFinset_iff]
  norm_num

example : (1 / 2 : ℚ).num * (1 / 3 : ℚ).den =
    (1 / 3 : ℚ).num * (1 / 2 : ℚ).den + 1 := by
  norm_num

example : (3 : ℕ) < (1 / 3 : ℚ).den + (1 / 2 : ℚ).den := by norm_num

example : mediant (1 / 3 : ℚ) (1 / 2 : ℚ) = (2 / 5 : ℚ) := by
  norm_num [mediant, Rat.divInt_eq_div]

example : mediant (1 / 3 : ℚ) (1 / 2 : ℚ) ∈ fareyFinset 5 := by
  rw [mem_fareyFinset_iff]
  norm_num [mediant, Rat.divInt_eq_div]

example :
    (1 / 3 : ℚ) < mediant (1 / 3 : ℚ) (1 / 2 : ℚ) ∧
      mediant (1 / 3 : ℚ) (1 / 2 : ℚ) < (1 / 2 : ℚ) := by
  norm_num [mediant, Rat.divInt_eq_div]

example : mediant (1 / 3 : ℚ) (1 / 2 : ℚ) ∉ fareyFinset 4 := by
  rw [mem_fareyFinset_iff]
  norm_num [mediant, Rat.divInt_eq_div]

example : IsFareyNeighbor 3 (1 / 3 : ℚ) (1 / 2 : ℚ) :=
  det_one_and_sum_gt_imp_neighbor 3 (1 / 3 : ℚ) (1 / 2 : ℚ)
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by norm_num) (by norm_num)

example (h : IsFareyNeighbor 3 (1 / 3 : ℚ) (1 / 2 : ℚ)) :
    (1 / 2 : ℚ).num * (1 / 3 : ℚ).den =
      (1 / 3 : ℚ).num * (1 / 2 : ℚ).den + 1 :=
  h.det_eq_one

example :
    IsFareyNeighbor 3 (1 / 3 : ℚ) (1 / 2 : ℚ) ↔
      (1 / 2 : ℚ).num * (1 / 3 : ℚ).den =
          (1 / 3 : ℚ).num * (1 / 2 : ℚ).den + 1 ∧
        3 < (1 / 3 : ℚ).den + (1 / 2 : ℚ).den :=
  isFareyNeighbor_iff_det_and_sum
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by rw [mem_fareyFinset_iff]; norm_num)

example : IsFareyNeighbor 3 (0 : ℚ) (1 / 3 : ℚ) :=
  det_one_and_sum_gt_imp_neighbor 3 0 (1 / 3 : ℚ)
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by norm_num) (by norm_num)

example : ¬ IsFareyNeighbor 3 (0 : ℚ) (2 / 3 : ℚ) := by
  intro h
  have := h.det_eq_one
  norm_num at this

example : mediant (1 / 3 : ℚ) (1 / 2 : ℚ) ∈ fareyFinset 5 :=
  mediant_mem_next_of_sum_eq 4 (1 / 3 : ℚ) (1 / 2 : ℚ)
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by rw [mem_fareyFinset_iff]; norm_num)
    (by norm_num)

example (h : IsFareyNeighbor 4 (1 / 3 : ℚ) (1 / 2 : ℚ)) :
    mediant (1 / 3 : ℚ) (1 / 2 : ℚ) ∈ fareyFinset 5 ∧
      mediant (1 / 3 : ℚ) (1 / 2 : ℚ) ∉ fareyFinset 4 :=
  h.mediant_mem_succ (by norm_num)

example (q : ℚ) :
    q ∈ fareyFinset 4 ↔
      q ∈ fareyFinset 3 ∨
        ∃ x y : ℚ, IsFareyNeighbor 3 x y ∧ x.den + y.den = 4 ∧ q = mediant x y :=
  farey_succ_generation (by norm_num) q

