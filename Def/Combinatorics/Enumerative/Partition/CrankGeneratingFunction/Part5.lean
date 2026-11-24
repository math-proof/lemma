module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/
namespace MetaMathlibExt

namespace CrankNonneg

noncomputable def crkMkPartition (L a : ℕ) (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : a + l.sum = L) : Nat.Partition L where
  parts := ((l : Multiset ℕ) + Multiset.replicate a 1)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with h | h
    · rw [Multiset.mem_coe] at h
      have hle := hpos i h
      omega
    · rw [Multiset.mem_replicate] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.one_pos
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_replicate, nsmul_eq_mul, mul_one,
      Nat.cast_id]
    omega

end CrankNonneg
end MetaMathlibExt
