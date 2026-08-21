import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {x y : α}
-- given
  (h : p x)
  (hxy : x = y) :
-- imply
  p y :=
-- proof
  hxy ▸ h


-- created on 2018-11-04
-- updated on 2026-08-20
