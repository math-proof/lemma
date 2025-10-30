import sympy.Basic


@[main]
private lemma main
-- given
  (n : ℕ) :
-- imply
  1 ≥ 1 % n := by
-- proof
  match n with
  | .zero =>
    simp
  | .succ n =>
    simp
    cases n <;> 
      simp


-- created on 2025-10-30
