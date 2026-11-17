module

public section


public theorem List.LengthDrop.eq.SubLength
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.drop i).length = s.length - i := by
-- proof
  simp


-- created on 2025-06-07
-- updated on 2026-10-26
