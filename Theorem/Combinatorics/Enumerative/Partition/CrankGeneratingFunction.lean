/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part2

public section

namespace MetaMathlibExt

namespace CrankNonneg

theorem crk_le_neg_impl {M k : ℕ} (P : Nat.Partition M) (hk : 1 ≤ k)
    (h : partitionCrank P ≤ -(k : ℤ)) :
    k ≤ Multiset.count 1 P.parts ∧ Multiset.count 1 P.parts ≠ 0 := by
  unfold partitionCrank at h
  split at h
  · next hc =>
      have h1 : (0 : ℤ) ≤ (P.parts.sup : ℤ) := by exact_mod_cast Nat.zero_le _
      omega
  · next hc =>
      have hnn : (0 : ℤ) ≤ (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℕ) : ℤ) := by
        exact_mod_cast Nat.zero_le _
      refine ⟨by omega, hc⟩

theorem crk_count_eq_zero_of_lt {k M : ℕ} (hk : 1 ≤ k) (hM : M < k) :
    crankLeCount k M = 0 := by
  unfold crankLeCount
  rw [Fintype.card_eq_zero_iff, isEmpty_iff]
  rintro ⟨P, hP⟩
  obtain ⟨hle, -⟩ := crk_le_neg_impl P hk hP
  have hc := crk_count_le P
  omega

end CrankNonneg
end MetaMathlibExt
