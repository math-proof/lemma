import sympy.Basic


@[main]
private lemma main
  {s : List α}
  {n : Nat}
-- given
  (h : n ≤ s.length) :
-- imply
  (s.take n |>.length) = n := by
-- proof
  induction s with
  | nil =>
    match n with
    | .zero =>
      simp [List.take]
    | .succ n =>
      have : n.succ ≤ 0 := h
      contradiction
  | cons =>
    match n with
    | .zero =>
      simp [List.take]
    | .succ n =>
      simp [List.take]
      apply Nat.le_of_succ_le_succ
      assumption


-- created on 2024-07-01
-- updated on 2025-03-29
