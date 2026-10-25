/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part2


namespace MetaMathlibExt.TwoDistantPolarized

open List

theorem sl_pairwise {n : ℕ} (p : Nat.Partition n) : (sl p).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem sl_sum {n : ℕ} (p : Nat.Partition n) : (sl p).sum = n := by
  rw [sl, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

theorem sl_mem {n : ℕ} (p : Nat.Partition n) (a : ℕ) : a ∈ sl p ↔ a ∈ p.parts :=
  Multiset.mem_sort _

theorem sl_pos {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ sl p, 0 < x := by
  intro x hx; exact p.parts_pos ((sl_mem p x).mp hx)

theorem sl_nodup_iff {n : ℕ} (p : Nat.Partition n) : (sl p).Nodup ↔ p.parts.Nodup := by
  rw [sl, ← Multiset.coe_nodup, Multiset.sort_eq]

end MetaMathlibExt.TwoDistantPolarized
