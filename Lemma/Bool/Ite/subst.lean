import sympy.Basic


@[path]
private lemma main
  {α β : Type*}
  {x y : α}
  {g : α → β}
  {b : β}
  {c : Prop} [Decidable c]
-- given
  (h : c → x = y) :
-- imply
  (if c then g x else b) = if c then g y else b := by
-- proof
  if hc : c then
    rw [if_pos hc, if_pos hc, h hc]
  else
    rw [if_neg hc, if_neg hc]


-- created on 2026-10-02
