import sympy.Basic


@[main]
private lemma main
  {s : List α}
  {n : Nat}
-- given
  (h : s.length ≥ n) :
-- imply
  (s.take n).length = n := by
-- proof
  induction s with
  | nil =>
    match n with
    | 0 =>
      simp [List.take]
    | n + 1 =>
      have : n.succ ≤ 0 := h
      contradiction
  | cons =>
    match n with
    | 0 =>
      simp [List.take]
    | n + 1 =>
      simp [List.take]
      apply Nat.le_of_succ_le_succ
      assumption


-- created on 2024-07-01
-- updated on 2025-03-29
