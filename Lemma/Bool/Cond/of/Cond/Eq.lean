import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {x y : α}
-- given
  (hxy : x = y)
  (h : p x) :
-- imply
  p y :=
-- proof
  hxy ▸ h


-- created on 2018-11-04
-- updated on 2026-08-20
