/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part7


namespace MetaMathlibExt.TwoDistantPolarized

open List

@[simp] theorem length_toBoff (j : ℕ) (Q : List ℕ) : (toBoff j Q).length = Q.length := by
  simp [toBoff]

theorem toBoff_Qof (j : ℕ) (o : List ℕ) : toBoff j (Qof j o) = o := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [toBoff, getElem_mapIdx, getElem_Qof]; omega

theorem toBoff_odd (j : ℕ) (Q : List ℕ) (hQ : ∀ x ∈ Q, x % 2 = 0)
    (hb : ∀ i (h : i < Q.length), 2 * (j + i) + 1 ≤ Q[i]) : ∀ x ∈ toBoff j Q, x % 2 = 1 := by
  intro x hx; rw [List.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < Q.length := by simpa using hi
  have hpar := hQ Q[i] (List.getElem_mem hi')
  have hbi := hb i hi'
  simp only [toBoff, getElem_mapIdx]; omega

theorem offset_staircase_bound (j : ℕ) (Q : List ℕ)
    (hpair : Q.Pairwise (fun a c => a + 2 ≤ c))
    (h0 : ∀ (hpos : 0 < Q.length), 2 * j + 1 ≤ Q[0]'hpos) (i : ℕ) (hi : i < Q.length) :
    2*(j+i)+1 ≤ Q[i] := by
  have hlen : 0 < Q.length := by omega
  have hb0 := h0 hlen
  have hcu := cumul Q hpair i hi 0 (by omega)
  simp only [Nat.sub_zero] at hcu
  omega

theorem Qof_toBoff (j : ℕ) (Q : List ℕ) (hpair : Q.Pairwise (fun a c => a + 2 ≤ c))
    (h0 : ∀ (hpos : 0 < Q.length), 2 * j + 1 ≤ Q[0]'hpos) : Qof j (toBoff j Q) = Q := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hbnd := offset_staircase_bound j Q hpair h0 i (by simpa using h1)
    simp only [getElem_Qof, toBoff, getElem_mapIdx]; omega

theorem gap_of_sameparity (L : List ℕ) (hs : L.Pairwise (· < ·)) (r : ℕ)
    (hp : ∀ x ∈ L, x % 2 = r) :
    L.Pairwise (fun a c => a + 2 ≤ c) := by
  rw [pairwise_iff_getElem] at hs ⊢
  intro i j hi hj hij
  have h1 := hp L[i] (List.getElem_mem hi)
  have h2 := hp L[j] (List.getElem_mem hj)
  have := hs i j hi hj hij
  omega

theorem sorted_eq_of_coe_eq (l₁ l₂ : List ℕ) (h₁ : l₁.Pairwise (· ≤ ·))
    (h₂ : l₂.Pairwise (· ≤ ·))
    (h : (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ)) : l₁ = l₂ := by
  rw [← sort_coe_self l₁ h₁, ← sort_coe_self l₂ h₂, h]

end MetaMathlibExt.TwoDistantPolarized
