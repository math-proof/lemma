import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_3.Part2
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.P_3_3_3c_existsUnique](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x: (Chapter3.Nat \ {(0:Object)}: Chapter3.Set)} :
-- imply
  ∃! y: Chapter3.Nat, P_3_3_3c x y :=
-- proof
  by
    -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
    -- sets converted to subtypes of `Object`, and subsets of those sets.
    obtain ⟨ x, hx ⟩ := x
    rw [SetTheory.Set.mem_sdiff, SetTheory.Set.mem_singleton] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    set n := ((⟨ x, hx1 ⟩:Chapter3.Nat):ℕ)
    have hnobj : x = (n:Object) := by simp [n]
    have hnpos : n ≠ 0 := by
      intro h
      apply hx2
      rw [hnobj, h]
      exact Object.ofnat_eq' (n := 0)
    apply ExistsUnique.intro ((n - 1 : ℕ):Chapter3.Nat)
    ·
      have hpred : (n - 1) + 1 = n := Nat.succ_pred_eq_of_ne_zero hnpos
      simp [P_3_3_3c, hnobj, hpred]
    intro y hy
    simp [P_3_3_3c, hnobj] at hy
    have hy' : (y:ℕ) + 1 = n := (Object.natCast_inj ((y:ℕ) + 1) n).mp hy
    have : (y:ℕ) = n - 1 := by omega
    exact (nat_equiv_symm_inj y ((n - 1 : ℕ):Chapter3.Nat)).mp (by simpa [nat_equiv_coe_of_coe] using this)


-- created on 2026-10-22
-- updated on 2026-10-23
