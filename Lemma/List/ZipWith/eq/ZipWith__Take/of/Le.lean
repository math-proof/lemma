import sympy.Basic


@[main]
private lemma main
  {a : List α}
  {b : List β}
-- given
  (h : a.length ≤ b.length)
  (f : α → β → γ) :
-- imply
  List.zipWith f a b = List.zipWith f a (b.take a.length) := by
-- proof
  induction a generalizing b with
  | nil =>
    -- Base case: b is empty, so the zipWith operation on a and b is empty.
    simp [List.zipWith]
  | cons y ys ih =>
    -- Inductive step: Assume the statement holds for ys, prove for y :: ys.
    cases b with
    | nil =>
      -- If a is empty, but h states a.length ≥ b.length, this is a contradiction.
      contradiction
    | cons x xs =>
      -- a is non-empty, so we can split it into x and xs.
      simp [List.zipWith]
      simp at h
      apply ih h


-- created on 2025-05-02
