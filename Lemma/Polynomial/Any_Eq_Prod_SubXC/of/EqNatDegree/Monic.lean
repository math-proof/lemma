import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Instance.Fun
import Notation.Fun
import Syntax.Fun
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
A monic polynomial over `ℂ` of degree `n` is a product of `n` monic linear factors.
-/
@[path]
private lemma main
  {n : ℕ}
  {q : ℂ[X]}
-- given
  (hm : q.Monic)
  (hd : q.natDegree = n) :
-- imply
  ∃ r : Fin n ⇀ ℂ, q = ∏ i : Fin n, (X - C r[i]) := by
-- proof
  induction n generalizing q with
  | zero =>
    have hq1 : q = 1 := (Monic.natDegree_eq_zero hm).mp hd
    refine ⟨⟨fun i => Fin.elim0 i⟩, ?_⟩
    simp [hq1]
  | succ n ih =>
    have hdeg : q.degree ≠ 0 := by
      rw [degree_eq_natDegree hm.ne_zero, hd]
      intro h
      exact Nat.succ_ne_zero n (WithBot.coe_injective h)
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root q hdeg
    obtain ⟨q', hq⟩ := (dvd_iff_isRoot (p := q) (a := α)).mpr hα
    have hqmonic : q'.Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C α) (by simpa [hq] using hm)
    have hqdeg : q'.natDegree = n := by
      have hmul := (monic_X_sub_C α).natDegree_mul hqmonic
      rw [← hq, hd, natDegree_X_sub_C] at hmul
      omega
    obtain ⟨r', hr'⟩ := ih hqmonic hqdeg
    refine ⟨⟨Fin.cons α fun i => r'[i]⟩, ?_⟩
    rw [Fin.prod_univ_succ, hq, hr']
    simp [Fin.cons_zero, Fin.cons_succ]


-- created on 2026-10-25
-- updated on 2026-10-27
