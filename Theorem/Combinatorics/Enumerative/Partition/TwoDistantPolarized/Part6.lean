/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part6


namespace MetaMathlibExt.TwoDistantPolarized

open List

theorem evenP_even (b : List ℕ) : ∀ x ∈ evenP b, x % 2 = 0 := by
  intro x hx; rw [evenP, List.mem_filter] at hx
  have h : x % 2 = 0 := by simpa using hx.2
  exact h

theorem oddP_odd (b : List ℕ) : ∀ x ∈ oddP b, x % 2 = 1 := by
  intro x hx; rw [oddP, List.mem_filter] at hx
  have h : x % 2 ≠ 0 := by simpa using hx.2
  omega

theorem evenP_pairwise (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (evenP b).Pairwise
    (· ≤ ·) := by
  rw [evenP]; exact hb.sublist List.filter_sublist

theorem oddP_pairwise (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (oddP b).Pairwise
    (· ≤ ·) := by
  rw [oddP]; exact hb.sublist List.filter_sublist

theorem split_perm (b : List ℕ) : (evenP b ++ oddP b).Perm b := by
  simpa [evenP, oddP] using List.filter_append_perm (fun x => decide (x % 2 = 0)) b

theorem fromB_odd (c : List ℕ) (hc : ∀ x ∈ c, x % 2 = 0) : ∀ x ∈ fromB c, x % 2 = 1 := by
  intro x hx; rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_fromB]
  have hi' : i < c.length := by simpa using hi
  have hmem := List.getElem_mem hi'
  have := hc _ hmem
  omega

theorem sum_polyParts (b : List ℕ) : (polyParts b).sum = b.sum + b.length ^ 2 := by
  rw [polyParts, List.sum_append, sum_fromB, sum_Qof]
  have hp := split_perm b
  have hs : (evenP b).sum + (oddP b).sum = b.sum := by
    have := hp.sum_eq; rw [List.sum_append] at this; omega
  have hl : (evenP b).length + (oddP b).length = b.length := by
    have := hp.length_eq; rw [List.length_append] at this; omega
  have hsq : (evenP b).length ^ 2 + (2 * (evenP b).length * (oddP b).length + (oddP b).length ^ 2)
       = b.length ^ 2 := by
    rw [← hl]; ring
  omega

theorem polyParts_pos (b : List ℕ) : ∀ x ∈ polyParts b, 0 < x := by
  intro x hx; rw [polyParts, List.mem_append] at hx
  rcases hx with h | h
  · exact fromB_pos _ x h
  · rw [List.mem_iff_getElem] at h; obtain ⟨i, hi, rfl⟩ := h
    rw [getElem_Qof]; omega

theorem polyParts_nodup (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (polyParts b).Nodup := by
  rw [polyParts, List.nodup_append]
  refine ⟨fromB_nodup _ (evenP_pairwise b hb), ?_, ?_⟩
  · exact (Qof_pairwise _ _ (oddP_pairwise b hb)).imp (fun h => by omega)
  · intro x hx y hy
    have hxo := fromB_odd _ (evenP_even b) x hx
    have hye := Qof_even _ _ (oddP_odd b) y hy
    omega

theorem polyParts_oddfilter (b : List ℕ) :
    (polyParts b).filter (fun a => decide (a % 2 = 1)) = fromB (evenP b) := by
  rw [polyParts, List.filter_append]
  have h1 : (fromB (evenP b)).filter (fun a => decide (a % 2 = 1)) = fromB (evenP b) := by
    apply List.filter_eq_self.mpr
    intro a ha; simp only [decide_eq_true_eq]
    exact fromB_odd _ (evenP_even b) a ha
  have h2 : (Qof (evenP b).length (oddP b)).filter (fun a => decide (a % 2 = 1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha; simp only [decide_eq_true_eq]
    have := Qof_even _ _ (oddP_odd b) a ha; omega
  rw [h1, h2, List.append_nil]

theorem polyParts_oddcard (b : List ℕ) :
    ((↑(polyParts b) : Multiset ℕ).filter (fun i => i % 2 = 1)).card = (evenP b).length := by
  rw [Multiset.filter_coe, Multiset.coe_card, polyParts_oddfilter, length_fromB]

theorem Qof_gt (j : ℕ) (o : List ℕ) (ho : ∀ x ∈ o, x % 2 = 1) : ∀ x ∈ Qof j o, 2 * j <
    x := by
  intro x hx; rw [List.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_Qof]
  have hi' : i < o.length := by simpa using hi
  have hmem := List.getElem_mem hi'
  have := ho _ hmem; omega

theorem polyParts_polarized (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) :
    (↑(polyParts b) : Multiset ℕ).Nodup ∧
    ∀ e ∈ (↑(polyParts b) : Multiset ℕ), e % 2 = 0 →
      2 * ((↑(polyParts b) : Multiset ℕ).filter (fun i => i % 2 = 1)).card < e := by
  refine ⟨by rw [Multiset.coe_nodup]; exact polyParts_nodup b hb, ?_⟩
  intro e he heven
  rw [polyParts_oddcard]
  rw [Multiset.mem_coe, polyParts, List.mem_append] at he
  rcases he with h | h
  · exact absurd (fromB_odd _ (evenP_even b) e h) (by omega)
  · exact Qof_gt _ _ (oddP_odd b) e h

end MetaMathlibExt.TwoDistantPolarized
