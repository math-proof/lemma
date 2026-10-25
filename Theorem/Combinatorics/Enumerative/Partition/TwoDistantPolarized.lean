/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized


namespace MetaMathlibExt.TwoDistantPolarized

open List

@[simp] theorem length_fromB (b : List ℕ) : (fromB b).length = b.length := by simp [fromB]

@[simp] theorem length_toB (L : List ℕ) : (toB L).length = L.length := by simp [toB]

theorem getElem_fromB (b : List ℕ) (i : ℕ) (h : i < (fromB b).length) :
    (fromB b)[i] = b[i]'(by simpa using h) + (2*i+1) := by
  simp [fromB, getElem_mapIdx]

theorem toB_fromB (b : List ℕ) : toB (fromB b) = b := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [toB, getElem_mapIdx, getElem_fromB]; omega

theorem sum_range_odd (m : ℕ) : ∑ i ∈ Finset.range m, (2*i+1) = m^2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

theorem sum_fromB (b : List ℕ) : (fromB b).sum = b.sum + b.length^2 := by
  rw [fromB, mapIdx_eq_ofFn, sum_ofFn]
  have : ∑ i : Fin b.length, (b.get i + (2 * (i:ℕ) + 1))
       = (∑ i : Fin b.length, b.get i) + ∑ i : Fin b.length, (2 * (i:ℕ) + 1) := by
    rw [Finset.sum_add_distrib]
  rw [this]
  congr 1
  · rw [← List.sum_ofFn, List.ofFn_get]
  · rw [Fin.sum_univ_eq_sum_range (fun i => 2*i+1), sum_range_odd]

theorem fromB_pairwise (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) :
    (fromB b).Pairwise (fun a c => a + 2 ≤ c) := by
  rw [pairwise_iff_getElem] at hb ⊢
  intro i j hi hj hij
  rw [getElem_fromB, getElem_fromB]
  have := hb i j (by simpa using hi) (by simpa using hj) hij
  omega

/-- cumulative 2-distant gap, indexed directly by `j` -/
theorem cumul (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c)) :
    ∀ j (hj : j < L.length) i (hij : i ≤ j), L[i]'(by omega) + 2 * (j - i) ≤ L[j] := by
  intro j
  induction j with
  | zero => intro hj i hij; interval_cases i; simp
  | succ e ih =>
    intro hj i hij
    rcases Nat.lt_or_ge i (e+1) with hlt | hge
    · have hie : i ≤ e := by omega
      have he : e < L.length := by omega
      have IH := ih he i hie
      have step := (pairwise_iff_getElem.mp hpair) e (e+1) (by omega) (by omega) (by omega)
      have : 2 * (e + 1 - i) = 2 * (e - i) + 2 := by omega
      omega
    · have : i = e + 1 := by omega
      subst this; simp

theorem staircase_bound (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c))
    (hpos : ∀ x ∈ L, 0 < x) (i : ℕ) (hi : i < L.length) : 2 * i + 1 ≤ L[i] := by
  have h0 : 0 < L[0]'(by omega) := hpos _ (List.getElem_mem (by omega))
  have hcu := cumul L hpair i hi 0 (by omega)
  simp only [Nat.sub_zero] at hcu
  omega

theorem fromB_toB (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c))
    (hpos : ∀ x ∈ L, 0 < x) : fromB (toB L) = L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hb := staircase_bound L hpair hpos i (by simpa using h1)
    simp only [getElem_fromB, toB, getElem_mapIdx]
    omega

theorem toB_pairwise (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c))
    (hpos : ∀ x ∈ L, 0 < x) : (toB L).Pairwise (· ≤ ·) := by
  rw [pairwise_iff_getElem]
  intro i j hi hj hij
  have hbi := staircase_bound L hpair hpos i (by simpa using hi)
  have hbj := staircase_bound L hpair hpos j (by simpa using hj)
  have hc := cumul L hpair j (by simpa using hj) i (by omega)
  simp only [toB, getElem_mapIdx]
  omega

theorem fromB_pos (b : List ℕ) : ∀ x ∈ fromB b, 0 < x := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_fromB]; omega

theorem fromB_nodup (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (fromB b).Nodup :=
  (fromB_pairwise b hb).imp (fun hac => by omega)

end MetaMathlibExt.TwoDistantPolarized
