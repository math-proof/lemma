module

public section


public theorem List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
  {a b : List α}
-- given
  (h₀ : a.length ≤ i)
  (h₁ : i < (a ++ b).length) :
-- imply
  have : i < a.length + b.length := by rwa [List.length_append] at h₁
  (a ++ b)[i] = b[i - a.length] := by
-- proof
  simp_all


-- created on 2025-05-15
-- updated on 2026-10-26
