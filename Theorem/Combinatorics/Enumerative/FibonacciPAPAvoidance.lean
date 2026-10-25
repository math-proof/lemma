/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Instance.Combinatorics.Enumerative.FibonacciPAPAvoidance


namespace MetaMathlibExt

theorem last_block {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    ∀ d, d ≤ N - (π (Fin.last N)).val →
      (π ⟨N - d, by omega⟩ : Fin (N+1)).val = (π (Fin.last N)).val + d := by
  obtain ⟨_, h312, h231⟩ := h
  set c := (π (Fin.last N)).val with hc
  have hcN : c ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro hd
    match d with
    | 0 =>
      simp only [Nat.sub_zero, Nat.add_zero]
      have : (⟨N, by omega⟩ : Fin (N+1)) = Fin.last N := by ext; simp
      rw [this]
    | (e+1) =>
      have hsum : c + e + 1 ≤ N := by omega
      set i0 : Fin (N+1) := ⟨N - (e+1), by omega⟩ with hi0
      have hplus : (π ⟨N - e, by omega⟩ : Fin (N+1)).val = c + e := IH e (by omega) (by omega)
      set a : ℕ := (π i0).val with ha
      have hge : c ≤ a := by
        by_contra hlt
        push Not at hlt
        set p : Fin (N+1) := π.symm ⟨c + e + 1, by omega⟩ with hp
        have hpv : (π p).val = c + e + 1 := by rw [hp]; simp
        have hpi : p.val < i0.val := by
          have hne : p ≠ i0 := by intro heq; rw [heq] at hpv; omega
          have hlt2 : p.val < N - e := by
            by_contra hge2
            push Not at hge2
            have hIHp := IH (N - p.val) (by omega) (by omega)
            have hpp : (⟨N - (N - p.val), by omega⟩ : Fin (N+1)) = p := by ext; simp; omega
            rw [hpp] at hIHp
            omega
          have hnev : p.val ≠ i0.val := fun hh => hne (Fin.ext hh)
          have hi0v : i0.val = N - (e+1) := by rw [hi0]
          omega
        have e1 : (π i0).val < (π ⟨N - e, by omega⟩ : Fin (N+1)).val := by rw [hplus, ← ha]; omega
        have e2 : (π ⟨N - e, by omega⟩ : Fin (N+1)).val < (π p).val := by rw [hplus, hpv]; omega
        have hik : i0.val < (⟨N - e, by omega⟩ : Fin (N+1)).val := by
          simp only [hi0, Fin.val_mk]; omega
        exact h312 p i0 ⟨N - e, by omega⟩ hpi hik ⟨e1, e2⟩
      have hge2 : c + e + 1 ≤ a := by
        rcases Nat.lt_or_ge a (c + e + 1) with hlt | hge3
        · exfalso
          set j : ℕ := a - c with hj
          have hjle : j ≤ e := by omega
          have hIHj := IH j (by omega) (by omega)
          have hval : (π ⟨N - j, by omega⟩ : Fin (N+1)).val = a := by rw [hIHj]; omega
          have heq : (⟨N - j, by omega⟩ : Fin (N+1)) = i0 := by
            apply π.injective; apply Fin.ext; rw [← ha]; exact hval
          have hcong : N - j = N - (e+1) := by
            have := congrArg Fin.val heq; simpa [hi0] using this
          omega
        · exact hge3
      have hle : a ≤ c + e + 1 := by
        by_contra hgt
        push Not at hgt
        set q : Fin (N+1) := π.symm ⟨c + e + 1, by omega⟩ with hq
        have hqv : (π q).val = c + e + 1 := by rw [hq]; simp
        have hqi : q.val < i0.val := by
          have hne : q ≠ i0 := by intro heq; rw [heq] at hqv; omega
          have hlt2 : q.val < N - e := by
            by_contra hge2
            push Not at hge2
            have hIHq := IH (N - q.val) (by omega) (by omega)
            have hqq : (⟨N - (N - q.val), by omega⟩ : Fin (N+1)) = q := by ext; simp; omega
            rw [hqq] at hIHq
            omega
          have hnev : q.val ≠ i0.val := fun hh => hne (Fin.ext hh)
          have hi0v : i0.val = N - (e+1) := by rw [hi0]
          omega
        have f1 : (π ⟨N - e, by omega⟩ : Fin (N+1)).val < (π q).val := by rw [hplus, hqv]; omega
        have f2 : (π q).val < (π i0).val := by rw [hqv, ← ha]; omega
        have hik : i0.val < (⟨N - e, by omega⟩ : Fin (N+1)).val := by
          simp only [hi0, Fin.val_mk]; omega
        exact h231 q i0 ⟨N - e, by omega⟩ hqi hik ⟨f1, f2⟩
      change a = c + (e + 1)
      omega

end MetaMathlibExt
