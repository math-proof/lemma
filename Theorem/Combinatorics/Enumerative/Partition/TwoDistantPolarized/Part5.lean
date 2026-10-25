/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part5


namespace MetaMathlibExt.TwoDistantPolarized

open List

@[simp] theorem length_Qof (j : ℕ) (o : List ℕ) : (Qof j o).length =
    o.length := by simp [Qof]

theorem getElem_Qof (j : ℕ) (o : List ℕ) (i : ℕ) (h : i < (Qof j o).length) :
    (Qof j o)[i] = o[i]'(by simpa using h) + (2*(j+i)+1) := by simp [Qof, getElem_mapIdx]

theorem sum_range_odd_off (j m : ℕ) : ∑ i ∈ Finset.range m, (2*(j+i)+1) = 2*j*m + m^2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

theorem sum_Qof (j : ℕ) (o : List ℕ) : (Qof j o).sum = o.sum +
    (2*j*o.length + o.length^2) := by
  rw [Qof, mapIdx_eq_ofFn, sum_ofFn]
  have : ∑ i : Fin o.length, (o.get i + (2 * (j + (i:ℕ)) + 1))
       = (∑ i : Fin o.length, o.get i) + ∑ i : Fin o.length, (2 * (j + (i:ℕ)) + 1) := by
    rw [Finset.sum_add_distrib]
  rw [this]; congr 1
  · rw [← List.sum_ofFn, List.ofFn_get]
  · rw [Fin.sum_univ_eq_sum_range (fun i => 2*(j+i)+1), sum_range_odd_off]

theorem Qof_pairwise (j : ℕ) (o : List ℕ) (ho : o.Pairwise (· ≤ ·)) :
    (Qof j o).Pairwise (fun a c => a + 2 ≤ c) := by
  rw [pairwise_iff_getElem] at ho ⊢
  intro p q hp hq hpq
  rw [getElem_Qof, getElem_Qof]
  have := ho p q (by simpa using hp) (by simpa using hq) hpq
  omega

theorem Qof_even (j : ℕ) (o : List ℕ) (ho : ∀ x ∈ o, x % 2 = 1) :
    ∀ x ∈ Qof j o, x % 2 = 0 := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_Qof]
  have hi' : i < o.length := by simpa using hi
  have := ho o[i] (List.getElem_mem hi')
  omega

end MetaMathlibExt.TwoDistantPolarized
