import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma push
  {x : ℂ}
  {k : ℕ}
-- given
  (h : k > 0) :
-- imply
  (x - k + 1) * (descPochhammer ℂ (k - 1)).eval x = (descPochhammer ℂ k).eval x := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [descPochhammer_succ_eval, Nat.add_sub_cancel]
  push_cast
  ring


@[main]
private lemma unshift
  {x : ℂ}
  {k : ℕ}
-- given
  (h : k > 0) :
-- imply
  x * (descPochhammer ℂ (k - 1)).eval (x - 1) = (descPochhammer ℂ k).eval x := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [descPochhammer_succ_left, Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]


-- created on 2026-09-27
