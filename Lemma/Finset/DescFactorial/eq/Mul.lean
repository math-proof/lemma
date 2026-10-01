import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma pop
  {x : ℂ}
  {k : ℕ}
-- given
  (h : k > 0) :
-- imply
  (descPochhammer ℂ k).eval x = (x - k + 1) * (descPochhammer ℂ (k - 1)).eval x := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [descPochhammer_succ_eval, Nat.add_sub_cancel]
  push_cast
  ring


@[main]
private lemma shift
  {x : ℂ}
  {k : ℕ}
-- given
  (h : k > 0) :
-- imply
  (descPochhammer ℂ k).eval x = x * (descPochhammer ℂ (k - 1)).eval (x - 1) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [descPochhammer_succ_left, Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]


-- created on 2026-09-27
