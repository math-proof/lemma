import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x = max x y) :
-- imply
  x ≥ y := by
-- proof
  calc _ ≤ max x y := le_max_right x y
    _ = x := h.symm


-- created on 2023-03-26
