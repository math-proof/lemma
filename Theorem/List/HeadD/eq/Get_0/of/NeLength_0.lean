module

public import Mathlib

public section


public theorem List.HeadD.eq.Get_0.of.NeLength_0
  {s : List α}
-- given
  (h : s.length ≠ 0)
  (default : α):
-- imply
  s.headD default = s[0] := by
-- proof
  match s with
  | .nil =>
    contradiction
  | .cons hd tl =>
    simp


-- created on 2024-07-01
-- updated on 2026-10-26
