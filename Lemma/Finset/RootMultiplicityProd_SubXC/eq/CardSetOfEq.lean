import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Instance.Fun
import Notation.Fun
import Syntax.Fun
import Initialize.Tactic.Attr.Basic
open Polynomial Finset


/--
The multiplicity of `z` in a product of linear factors is the number of factors with that root.
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (r : Fin n ⇀ ℂ)
  (z : ℂ) :
-- imply
  (∏ i : Fin n, (X - C r[i])).rootMultiplicity z =
    Finset.card {i : Fin n | r[i] = z} := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hne :
      (X - C r[0]) * ∏ i : Fin n, (X - C r[i.succ]) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _)
        (prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _)
    rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C, ih ⟨fun i => r[i.succ]⟩]
    classical
    have hcard :
      Finset.card {i : Fin (n + 1) | r[i] = z} =
          (if r[0] = z then 1 else 0) +
            Finset.card {i : Fin n | r[i.succ] = z} := by
      rw [card_eq_sum_ones, sum_filter, Fin.sum_univ_succ, ← sum_filter,
        ← card_eq_sum_ones]
    rw [hcard]
    if h0 : r[0] = z then
      rw [ite_eq_left h0, ite_eq_left h0.symm]
    else
      rw [ite_eq_right h0, ite_eq_right (Ne.symm h0)]


-- created on 2026-10-25
-- updated on 2026-10-27
