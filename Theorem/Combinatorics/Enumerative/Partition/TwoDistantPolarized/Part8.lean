/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part8


namespace MetaMathlibExt.TwoDistantPolarized

open List

theorem Pl_mem {n : ℕ} (p : Nat.Partition n) (x : ℕ) : x ∈ Pl p ↔ x ∈ p.parts ∧ x % 2 =
    1 := by
  rw [Pl, Multiset.mem_sort, oddm, Multiset.mem_filter]

theorem Ql_mem {n : ℕ} (p : Nat.Partition n) (x : ℕ) : x ∈ Ql p ↔ x ∈ p.parts ∧ x % 2 =
    0 := by
  rw [Ql, Multiset.mem_sort, evenm, Multiset.mem_filter]

theorem Pl_odd {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Pl p, x % 2 = 1 :=
  fun x hx => ((Pl_mem p x).mp hx).2

theorem Ql_even {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Ql p, x % 2 = 0 :=
  fun x hx => ((Ql_mem p x).mp hx).2

theorem Pl_pos {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Pl p, 0 < x :=
  fun x hx => p.parts_pos ((Pl_mem p x).mp hx).1

theorem Ql_pos {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Ql p, 0 < x :=
  fun x hx => p.parts_pos ((Ql_mem p x).mp hx).1

theorem Pl_le {n : ℕ} (p : Nat.Partition n) : (Pl p).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort _ _

theorem Ql_le {n : ℕ} (p : Nat.Partition n) : (Ql p).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort _ _

theorem Pl_strict {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) : (Pl p).Pairwise
    (· < ·) := by
  apply sorted_nodup_strict _ (Pl_le p)
  rw [Pl, ← Multiset.coe_nodup, Multiset.sort_eq]
  exact hnd.filter _

theorem Ql_strict {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) : (Ql p).Pairwise
    (· < ·) := by
  apply sorted_nodup_strict _ (Ql_le p)
  rw [Ql, ← Multiset.coe_nodup, Multiset.sort_eq]
  exact hnd.filter _

theorem Pl_gap {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) :
    (Pl p).Pairwise (fun a c => a + 2 ≤ c) := gap_of_sameparity _ (Pl_strict p hnd) 1 (Pl_odd p)

theorem Ql_gap {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) :
    (Ql p).Pairwise (fun a c => a + 2 ≤ c) := gap_of_sameparity _ (Ql_strict p hnd) 0 (Ql_even p)

theorem sortsum (m : Multiset ℕ) : (m.sort (· ≤ ·)).sum = m.sum := by
  rw [← Multiset.sum_coe, Multiset.sort_eq]

theorem oddm_add_evenm {n : ℕ} (p : Nat.Partition n) : oddm p + evenm p = p.parts := by
  have hev : evenm p = p.parts.filter (fun x => ¬ x % 2 = 1) := by
    rw [evenm]; apply Multiset.filter_congr; intro x _; omega
  rw [oddm, hev]; exact Multiset.filter_add_not _ _

theorem Ql_bound {n : ℕ} (p : Nat.Partition n)
    (hpol : ∀ e ∈ p.parts, e % 2 = 0 → 2 * (p.parts.filter (fun i => i % 2 = 1)).card < e) :
    ∀ (hpos : 0 < (Ql p).length), 2 * (Pl p).length + 1 ≤ (Ql p)[0]'hpos := by
  intro hpos
  have hmem := List.getElem_mem hpos
  have h1 := (Ql_mem p _).mp hmem
  have hlt := hpol _ h1.1 h1.2
  have hcard : (p.parts.filter (fun i => i % 2 = 1)).card = (Pl p).length := by
    rw [Pl, Multiset.length_sort, oddm]
  omega

end MetaMathlibExt.TwoDistantPolarized
