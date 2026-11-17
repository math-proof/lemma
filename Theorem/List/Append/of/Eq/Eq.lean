module

public section


public theorem List.Append.of.Eq.Eq
  {a b a' b': List α}
-- given
  (h : a = b)
  (h' : a' = b') :
-- imply
  a ++ a' = b ++ b' := by
-- proof
  rw [h, h']


-- created on 2025-06-17
