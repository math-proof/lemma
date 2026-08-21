import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p) :
-- imply
  (q → p) ∧ (¬q → p) :=
-- proof
  ⟨fun _ => h, fun _ => h⟩


-- created on 2018-08-13
-- updated on 2026-08-20
