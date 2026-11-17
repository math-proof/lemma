module

public section


public theorem List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
  {s : List α}
  {i : ℕ}
-- given
  (h : i < s.length - 1):
-- imply
  s.tail.eraseIdx i = (s.eraseIdx (i + 1)).tail := by
-- proof
  cases s with
  | nil =>
    simp at h
  | cons a as =>
    rw [List.eraseIdx_cons_succ]
    simp only [List.tail_cons]

-- created on 2025-06-22
