import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ∧ q)
  (left : Bool := true) :
-- imply
  match left with
  | true => p
  | false => q := by
-- proof
  match left with
  | true =>
    exact h.left
  | false =>
    exact h.right


-- created on 2024-07-01
