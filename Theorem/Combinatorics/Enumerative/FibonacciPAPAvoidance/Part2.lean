/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Def.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part2


namespace MetaMathlibExt

lemma buildPerm_lt {m L : ℕ} (ρ : Equiv.Perm (Fin m)) (x : Fin (m + L)) (h : x.val < m) :
    (buildPerm m L ρ x).val = (ρ ⟨x.val, h⟩).val := by
  simp only [buildPerm, Equiv.coe_fn_mk, dite_eq_left h]

lemma buildPerm_ge {m L : ℕ} (ρ : Equiv.Perm (Fin m)) (x : Fin (m + L)) (h : m ≤ x.val) :
    (buildPerm m L ρ x).val = 2*m + L - 1 - x.val := by
  have hn : ¬ x.val < m := by omega
  simp only [buildPerm, Equiv.coe_fn_mk, dite_eq_right hn]

theorem buildPerm_good {m L : ℕ} (ρ : Equiv.Perm (Fin m)) (hρ : IsGood m ρ)
    (hL : L % 2 = 1) : IsGood (m + L) (buildPerm m L ρ) := by
  obtain ⟨hpar, h312, h231⟩ := hρ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases h : i.val < m
    · rw [buildPerm_lt ρ i h]; exact hpar ⟨i.val, h⟩
    · rw [buildPerm_ge ρ i (by omega)]
      have hib : i.val < m + L := i.isLt
      omega
  · intro i j k hij hjk ⟨hjk', hki'⟩
    by_cases hk : k.val < m
    · have hi : i.val < m := by omega
      have hj : j.val < m := by omega
      refine h312 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk ?_
      rw [← buildPerm_lt ρ i hi, ← buildPerm_lt ρ j hj, ← buildPerm_lt ρ k hk]
      exact ⟨hjk', hki'⟩
    · have hkge : m ≤ k.val := by omega
      have hkval : (buildPerm m L ρ k).val = 2*m + L - 1 - k.val := buildPerm_ge ρ k hkge
      have hige : m ≤ i.val := by
        by_contra hlt
        push Not at hlt
        have e1 : (buildPerm m L ρ i).val = (ρ ⟨i.val, hlt⟩).val := buildPerm_lt ρ i hlt
        have e2 := (ρ ⟨i.val, hlt⟩).isLt
        have := k.isLt
        omega
      have hjge : m ≤ j.val := by omega
      have hival : (buildPerm m L ρ i).val = 2*m + L - 1 - i.val := buildPerm_ge ρ i hige
      have hjval : (buildPerm m L ρ j).val = 2*m + L - 1 - j.val := buildPerm_ge ρ j hjge
      have := i.isLt; have := j.isLt; have := k.isLt
      omega
  · intro i j k hij hjk ⟨hki', hij'⟩
    by_cases hk : k.val < m
    · have hi : i.val < m := by omega
      have hj : j.val < m := by omega
      refine h231 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk ?_
      rw [← buildPerm_lt ρ i hi, ← buildPerm_lt ρ j hj, ← buildPerm_lt ρ k hk]
      exact ⟨hki', hij'⟩
    · have hkge : m ≤ k.val := by omega
      have hkval : (buildPerm m L ρ k).val = 2*m + L - 1 - k.val := buildPerm_ge ρ k hkge
      have hige : m ≤ i.val := by
        by_contra hlt
        push Not at hlt
        have e1 : (buildPerm m L ρ i).val = (ρ ⟨i.val, hlt⟩).val := buildPerm_lt ρ i hlt
        have e2 := (ρ ⟨i.val, hlt⟩).isLt
        have := k.isLt
        omega
      have hjge : m ≤ j.val := by omega
      have hival : (buildPerm m L ρ i).val = 2*m + L - 1 - i.val := buildPerm_ge ρ i hige
      have hjval : (buildPerm m L ρ j).val = 2*m + L - 1 - j.val := buildPerm_ge ρ j hjge
      have := i.isLt; have := j.isLt; have := k.isLt
      omega

lemma block_val {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (N + 1))
    (hi : (π (Fin.last N)).val ≤ i.val) :
    (π i).val = (π (Fin.last N)).val + N - i.val := by
  have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
  have hlb := last_block π h (N - i.val) (by omega)
  have hpos : (⟨N - (N - i.val), by omega⟩ : Fin (N+1)) = i := by ext; simp; omega
  rw [hpos] at hlb
  omega

lemma front_val {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (N + 1))
    (hi : i.val < (π (Fin.last N)).val) : (π i).val < (π (Fin.last N)).val := by
  set c := (π (Fin.last N)).val with hc
  by_contra hge
  push Not at hge
  have hv : (π i).val ≤ N := Nat.lt_succ_iff.mp (π i).isLt
  set v := (π i).val with hv2
  have hjlt : c + N - v < N + 1 := by omega
  have hbj := block_val π h ⟨c + N - v, hjlt⟩ (by simp only; omega)
  have hval : (π ⟨c + N - v, hjlt⟩).val = v := by rw [hbj]; simp only; omega
  have heq : (⟨c + N - v, hjlt⟩ : Fin (N+1)) = i := by
    apply π.injective; apply Fin.ext; rw [hval]
  have := congrArg Fin.val heq
  simp only at this
  omega

lemma front_symm {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (N + 1))
    (hi : i.val < (π (Fin.last N)).val) : (π.symm i).val < (π (Fin.last N)).val := by
  set c := (π (Fin.last N)).val with hc
  by_contra hge
  push Not at hge
  have hbv := block_val π h (π.symm i) hge
  rw [Equiv.apply_symm_apply] at hbv
  have hb : (π.symm i).val ≤ N := Nat.lt_succ_iff.mp (π.symm i).isLt
  omega

end MetaMathlibExt
