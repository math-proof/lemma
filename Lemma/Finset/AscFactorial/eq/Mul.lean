import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma pop
  {x : ℂ}
  {k : ℕ}
-- given
  (h : k > 0) :
-- imply
  (ascPochhammer ℂ k).eval x = (x + k - 1) * (ascPochhammer ℂ (k - 1)).eval x := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [ascPochhammer_succ_eval, Nat.add_sub_cancel]
  push_cast
  ring


@[path]
private lemma shift
  {x : ℂ}
  {k : ℕ}
-- given
  (h : k > 0) :
-- imply
  (ascPochhammer ℂ k).eval x = x * (ascPochhammer ℂ (k - 1)).eval (x + 1) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [ascPochhammer_succ_left, Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]


-- created on 2023-08-17
