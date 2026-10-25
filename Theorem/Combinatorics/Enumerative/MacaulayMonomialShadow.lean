/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple


namespace MetaMathlibExt

open BigOperators

section

/-- A binomial coefficient on the `r`th diagonal eventually exceeds any given natural. -/
lemma mms_lt_choose_add (r n : ℕ) (hr : 0 < r) :
    n < Nat.choose (n + r) r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      n < Nat.choose (n + (t + 1)) (t + 1) := by
        simpa only [Nat.succ_eq_add_one] using ih (by omega)
      _ ≤ Nat.choose (n + (t + 2)) (t + 2) := by
        rw [show n + (t + 2) = (n + (t + 1)).succ by omega,
          show t + 2 = (t + 1).succ by omega, Nat.choose_succ_succ]
        exact Nat.le_add_right _ _

/-- Appending a larger value to a strictly increasing finite tuple preserves strictness. -/
lemma mms_strictMono_snoc {r d : ℕ} {f : Fin r → ℕ} (hf : StrictMono f)
    (hlt : ∀ i, f i < d) : StrictMono (Fin.snoc f d) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hxy)
  rcases y.eq_castSucc_or_eq_last with ⟨y, rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc] using
      hf (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hxy))
  · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hlt x

/-- Every number below one binomial coefficient has a bounded strict cascade. -/
lemma mms_exists_rep_lt (r bound n : ℕ) (hn : n < Nat.choose bound r) :
    ∃ digits : Fin r → ℕ, StrictMono digits ∧ (∀ i, digits i < bound) ∧
      n = ∑ i, Nat.choose (digits i) (i.1 + 1) := by
  induction r generalizing bound n with
  | zero =>
    have hn0 : n = 0 := by
      simp only [Nat.choose_zero_right] at hn
      omega
    subst n
    refine ⟨Fin.elim0, ?_, ?_, by simp⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ r ih =>
    let P : ℕ → Prop := fun x => Nat.choose x (r + 1) ≤ n
    let d := Nat.findGreatest P (bound - 1)
    have hbound : 0 < bound := by
      by_contra! h
      have hb : bound = 0 := by omega
      subst bound
      simp at hn
    have hdbound : d < bound := by
      have := Nat.findGreatest_le (P := P) (bound - 1)
      omega
    have hdle : Nat.choose d (r + 1) ≤ n := by
      change P d
      apply Nat.findGreatest_spec (m := 0)
      · omega
      · simp [P]
    have hnext : n < Nat.choose (d + 1) (r + 1) := by
      by_cases h : d + 1 < bound
      · have hnot : ¬P (d + 1) := by
          apply Nat.findGreatest_is_greatest (P := P) (n := bound - 1)
          · change d < d + 1
            omega
          · omega
        simpa [P, Nat.not_le] using hnot
      · have hdb : d + 1 = bound := by omega
        simpa [hdb] using hn
    have hrem : n - Nat.choose d (r + 1) < Nat.choose d r := by
      rw [show d + 1 = d.succ by omega, show r + 1 = r.succ by omega,
        Nat.choose_succ_succ] at hnext
      exact (Nat.sub_lt_iff_lt_add hdle).2 hnext
    obtain ⟨lower, hlower, hlowerd, hsum⟩ :=
      ih d (n - Nat.choose d (r + 1)) hrem
    refine ⟨Fin.snoc lower d, mms_strictMono_snoc hlower hlowerd, ?_, ?_⟩
    · intro i
      rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using (hlowerd i).trans hdbound
      · simpa only [Fin.snoc_last] using hdbound
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      rw [← hsum]
      omega

/-- Every natural has a strict `r`-binomial cascade when `r` is positive. -/
lemma mms_exists_rep (r n : ℕ) (hr : 0 < r) :
    ∃ digits : Fin r → ℕ, StrictMono digits ∧
      n = ∑ i, Nat.choose (digits i) (i.1 + 1) := by
  obtain ⟨digits, hstrict, -, hsum⟩ :=
    mms_exists_rep_lt r (n + r) n (mms_lt_choose_add r n hr)
  exact ⟨digits, hstrict, hsum⟩

end
end MetaMathlibExt
