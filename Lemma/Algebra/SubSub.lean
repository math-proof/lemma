import sympy.Basic


@[main]
private lemma comm.nat
  {a b c : ℕ} :
-- imply
  a - b - c = a - c - b := by
-- proof
  simp [Nat.sub_sub, add_comm]


/--
This lemma demonstrates that in an additive commutative group, the order of subtraction of two elements does not affect the result.
Specifically, it shows that subtracting `b` and then `c` from `a` yields the same value as subtracting `c` and then `b`, leveraging the commutativity of the group operation.
-/
@[main]
private lemma Comm
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - b - c = a - c - b := by
-- proof
  abel


-- created on 2025-06-06
