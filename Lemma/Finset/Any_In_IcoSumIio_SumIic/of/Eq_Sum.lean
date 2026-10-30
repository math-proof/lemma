import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Notation.Fun
import Initialize.Tactic.Attr.Basic


/--
Every index lies in some block of a partition of `Fin n`.
-/
@[path]
private lemma main
  {n m : ℕ}
  {d : Fin n ⇀ ℕ}
-- given
  (hsum : ∑ k : Fin n, d[k] = m)
  (i : Fin m) :
-- imply
  ∃ k : Fin n, (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d[j]) (∑ j ∈ Finset.Iic k, d[j]) := by
-- proof
  if hn : n = 0 then
    have hm : m = 0 := by
      simpa [hn] using hsum.symm
    have hi : (i : ℕ) < m := i.isLt
    omega
  else
    let last : Fin n := ⟨n - 1, by omega⟩
    have hlast : ∑ j ∈ Finset.Iic last, d[j] = m := by
      convert hsum using 2
      ext j
      simp [Finset.mem_Iic, Fin.le_def, last]
      have := j.isLt
      omega
    let S := Finset.univ.filter fun k : Fin n => (i : ℕ) < ∑ j ∈ Finset.Iic k, d[j]
    have hS : S.Nonempty := by
      refine ⟨last, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hlast]
      exact i.isLt
    let k := S.min' hS
    have hklt : (i : ℕ) < ∑ j ∈ Finset.Iic k, d[j] := by
      have hkmem := Finset.min'_mem S hS
      simp only [S, Finset.mem_filter] at hkmem
      exact hkmem.2
    have hlt' : ¬ (i : ℕ) < ∑ j ∈ Finset.Iio k, d[j] := by
      by_contra hlt
      have hkpos : 0 < (k : ℕ) := by
        by_contra hk0
        have hk0' : (k : ℕ) = 0 := by omega
        have hempty : Finset.Iio k = ∅ := by
          ext j
          simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, Fin.lt_def]
          omega
        simp [hempty] at hlt
      let k' : Fin n := ⟨(k : ℕ) - 1, by omega⟩
      have hk'val : (k' : ℕ) = (k : ℕ) - 1 := rfl
      have hI : Finset.Iic k' = Finset.Iio k := by
        ext j
        rw [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def]
        omega
      have hk'mem : k' ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [hI]
      have hlemin : (k : ℕ) ≤ k' := by
        have hle := Finset.min'_le S k' hk'mem
        rwa [Fin.le_def] at hle
      have hltk : (k' : ℕ) < k := by
        rw [hk'val]
        omega
      omega
    refine ⟨k, ?_⟩
    simp only [Finset.mem_Ico]
    exact ⟨by omega, hklt⟩


-- created on 2026-10-25
