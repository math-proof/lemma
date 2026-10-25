/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part4


namespace MetaMathlibExt

namespace CrankNonneg

/-! ## Pair representation -/

theorem crk_nonOne_mem {n : ℕ} (P : Nat.Partition n) (x : ℕ) :
    x ∈ nonOneParts P ↔ x ∈ P.parts ∧ 2 ≤ x := by
  unfold nonOneParts
  rw [Multiset.mem_sort, Multiset.mem_filter]

theorem crk_nonOne_sorted {n : ℕ} (P : Nat.Partition n) :
    (nonOneParts P).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

theorem crk_nonOne_ge_two {n : ℕ} (P : Nat.Partition n) :
    ∀ x ∈ nonOneParts P, 2 ≤ x := by
  intro x hx
  exact ((crk_nonOne_mem P x).mp hx).2

theorem crk_parts_eq_nonOne_add {n : ℕ} (P : Nat.Partition n) :
    P.parts = ((nonOneParts P : Multiset ℕ) + Multiset.replicate (Multiset.count 1 P.parts) 1) := by
  have hsort : ((nonOneParts P : Multiset ℕ)) = P.parts.filter (2 ≤ ·) := by
    rw [nonOneParts, Multiset.sort_eq]
  rw [hsort]
  have hcomp : P.parts.filter (fun x => ¬ 2 ≤ x) =
      Multiset.replicate (Multiset.count 1 P.parts) 1 := by
    have hcongr : P.parts.filter (fun x => ¬ 2 ≤ x) = P.parts.filter (· = 1) := by
      apply Multiset.filter_congr
      intro x hx
      have hpos := P.parts_pos hx
      omega
    rw [hcongr, Multiset.filter_eq']
  conv_lhs => rw [← Multiset.filter_add_not (2 ≤ ·) P.parts]
  rw [hcomp]

theorem crk_omega_add_sum {n : ℕ} (P : Nat.Partition n) :
    Multiset.count 1 P.parts + (nonOneParts P).sum = n := by
  have h := congrArg Multiset.sum (crk_parts_eq_nonOne_add P)
  rw [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_replicate, nsmul_eq_mul, mul_one,
    Nat.cast_id, P.parts_sum] at h
  omega

theorem crk_decode {n : ℕ} (l : List ℕ) (hl : l.Pairwise (· ≥ ·))
    (h2 : ∀ x ∈ l, 2 ≤ x) (a : ℕ) (P : Nat.Partition n)
    (hP : P.parts = ((l : Multiset ℕ) + Multiset.replicate a 1)) :
    Multiset.count 1 P.parts = a ∧ nonOneParts P = l := by
  have hcount : Multiset.count 1 ((l : Multiset ℕ)) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    rw [Multiset.mem_coe] at hmem
    have hle := h2 1 hmem
    omega
  have hω : Multiset.count 1 P.parts = a := by
    rw [hP, Multiset.count_add, hcount, Multiset.count_replicate_self, Nat.zero_add]
  refine ⟨hω, ?_⟩
  have hfil : P.parts.filter (2 ≤ ·) = ((l : Multiset ℕ)) := by
    rw [hP, Multiset.filter_add]
    have h1 : ((l : Multiset ℕ)).filter (2 ≤ ·) = ((l : Multiset ℕ)) := by
      rw [Multiset.filter_eq_self]
      intro x hx
      rw [Multiset.mem_coe] at hx
      exact h2 x hx
    have h0 : (Multiset.replicate a 1).filter (2 ≤ ·) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      rw [Multiset.mem_replicate] at hx
      obtain ⟨-, rfl⟩ := hx
      omega
    rw [h1, h0, Multiset.add_zero]
  unfold nonOneParts
  rw [hfil, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hl

end CrankNonneg
end MetaMathlibExt
