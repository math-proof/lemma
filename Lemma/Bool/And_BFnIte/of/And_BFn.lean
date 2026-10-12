import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b c : α}
-- given
  (hp : p)
  (h : (if p then a else b) = c) :
-- imply
  a = c := by
-- proof
  rwa [ite_eq_left hp] at h


-- created on 2018-01-19
-- updated on 2026-10-12
