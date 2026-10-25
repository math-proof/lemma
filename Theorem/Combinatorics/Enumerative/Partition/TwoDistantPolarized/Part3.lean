/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part3


namespace MetaMathlibExt.TwoDistantPolarized

open List

@[simp] theorem ofList_parts {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hsum : L.sum = n)
    :
    (ofList L hpos hsum).parts = (L : Multiset ℕ) := rfl

-- sort of an already weakly-sorted list is itself
theorem sort_coe_self (L : List ℕ) (h : L.Pairwise (· ≤ ·)) :
    (L : Multiset ℕ).sort (· ≤ ·) = L := by
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ h

-- strictly sorted from sorted + nodup
theorem sorted_nodup_strict (L : List ℕ) (hs : L.Pairwise (· ≤ ·)) (hn : L.Nodup) :
    L.Pairwise (· < ·) := by
  have := hs.and hn
  exact this.imp (fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne)

theorem pairwise_iff_mempairs (L : List ℕ) (hstrict : L.Pairwise (· < ·)) (P : ℕ → ℕ → Prop)
    :
    L.Pairwise P ↔ ∀ a ∈ L, ∀ b ∈ L, a < b → P a b := by
  constructor
  · intro hp a ha b hb hab
    rw [List.mem_iff_getElem] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    have hij : i < j := by
      rcases lt_trichotomy i j with h | h | h
      · exact h
      · subst h; exact absurd hab (lt_irrefl _)
      · exact absurd hab (not_lt.mpr (le_of_lt ((pairwise_iff_getElem.mp hstrict) j i hj hi h)))
    exact (pairwise_iff_getElem.mp hp) i j hi hj hij
  · intro h
    rw [pairwise_iff_getElem]
    intro i j hi hj hij
    exact h _ (List.getElem_mem hi) _ (List.getElem_mem hj)
      ((pairwise_iff_getElem.mp hstrict) i j hi hj hij)

/-- the theorem's 2-distant predicate ↔ pairwise 2-gap on the sorted list -/
theorem hA_iff {n : ℕ} (p : Nat.Partition n) :
    (p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b) ↔
      (sl p).Pairwise (fun a c => a + 2 ≤ c) := by
  constructor
  · rintro ⟨hnd, hgap⟩
    have hstrict := sorted_nodup_strict _ (sl_pairwise p) ((sl_nodup_iff p).mpr hnd)
    rw [pairwise_iff_mempairs _ hstrict]
    intro a ha b hb hab
    exact hgap a ((sl_mem p a).mp ha) b ((sl_mem p b).mp hb) hab
  · intro hpw
    have hstrict : (sl p).Pairwise (· < ·) := hpw.imp (fun h => by omega)
    have hnd : p.parts.Nodup := (sl_nodup_iff p).mp hstrict.nodup
    refine ⟨hnd, ?_⟩
    intro a ha b hb hab
    have := (pairwise_iff_mempairs _ hstrict (fun a c => a + 2 ≤ c)).mp hpw
    exact this a ((sl_mem p a).mpr ha) b ((sl_mem p b).mpr hb) hab

end MetaMathlibExt.TwoDistantPolarized
