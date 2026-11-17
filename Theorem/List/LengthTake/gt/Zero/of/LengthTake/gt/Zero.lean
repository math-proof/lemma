module

public section


public theorem List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
  {s : List α}
  {n : ℕ}
-- given
  (h : (s.take n).length > 0) :
-- imply
  s.length > 0 := by
-- proof
  by_contra h'
  simp at h'
  rw [h'] at h
  simp at h


-- created on 2025-06-15
