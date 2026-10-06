import Mathlib
import sympy.Basic

open Polynomial

/--
[Polynomial_finite_setOf_criticalValue](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_finite_setOf_criticalValue.lean)
-/
@[main]
private lemma main
  {k : Type u} [Field k]
  {P : k[X]}
-- given
  (hP : derivative P ≠ 0) :
-- imply
  {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite := by
-- proof
  have hfin : {x : k | (derivative P).eval x = 0}.Finite := (derivative P).finite_setOfPred_isRoot hP
  refine (hfin.image fun x => P.eval x).subset ?_
  rintro c ⟨x, rfl, hx⟩
  exact ⟨x, hx, rfl⟩


-- created on 2026-10-05
