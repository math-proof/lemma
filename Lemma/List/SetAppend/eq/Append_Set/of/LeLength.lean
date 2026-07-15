import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h_s : a.length ≤ i)
  (b : List α)
  (x : α) :
-- imply
  (a ++ b).set i x = a ++ b.set (i - a.length) x :=
-- proof
  List.set_append_right i x h_s


-- created on 2026-07-15
