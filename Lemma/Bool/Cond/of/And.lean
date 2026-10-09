import sympy.Basic


@[path]
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


@[path]
private lemma subst
  {a b : α}
  {p : α → Prop}
-- given
  (h : p b ∧ a = b) :
-- imply
  p a := by
-- proof
  rw [h.2]
  exact h.1


-- created on 2018-01-02
-- updated on 2026-09-27
