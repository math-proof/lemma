module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.EqEraseIdx.of.LeLength
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length ≤ i) :
-- imply
  s.eraseIdx i = s :=
-- proof
  List.eraseIdx_of_length_le h


-- created on 2025-06-23
