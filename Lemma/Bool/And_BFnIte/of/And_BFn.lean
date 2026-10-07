import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {p : Prop} [Decidable p]
  {a b c : α}
-- given
  (hp : p)
  (h : (if p then a else b) = c) :
-- imply
  a = c := by
-- proof
  rw [if_pos hp] at h
  exact h


-- created on 2026-10-03
