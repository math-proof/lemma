import Batteries.Data.List.Lemmas
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
  match s with
  | [] =>
    simp
  | [_] =>
    grind [List.swap_eq]
  | _ :: _ :: _ =>
    simp at h


-- created on 2026-07-22
-- updated on 2026-08-24
