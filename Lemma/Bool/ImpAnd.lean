import sympy.Basic


@[main]
private lemma main
  (left : Bool := true) :
-- imply
  match left with
  | true =>
    p ∧ q → p
  | false =>
    q ∧ p → p := by
-- proof
  cases left <;>
    tauto

-- created on 2025-04-10
