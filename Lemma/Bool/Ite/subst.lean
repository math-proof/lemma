import sympy.Basic


@[path]
private lemma main
  {c : Prop} [Decidable c]
  {x y : α}
  {g : α → β}
  {b : β}
-- given
  (h : c → x = y) :
-- imply
  (if c then g x else b) = if c then g y else b := by
-- proof
  if hc : c then
    rw [ite_eq_left hc, ite_eq_left hc, h hc]
  else
    rw [ite_eq_right hc, ite_eq_right hc]


-- created on 2018-02-04
-- updated on 2026-10-12
