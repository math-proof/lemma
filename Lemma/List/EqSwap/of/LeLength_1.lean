import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ 1)
  (i j : ℕ) :
-- imply
  s.swap i j = s := by
-- proof
  match h : s with
  | [] =>
    unfold List.swap
    simp
  | [x] =>
    unfold List.swap
    grind


-- created on 2026-07-22
