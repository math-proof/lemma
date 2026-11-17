module

public import Theorem.Nat.AddAdd

public section

open Nat


public theorem List.EraseIdxAppend.eq.Append_EraseIdx
-- given
  (a b : List α)
  (i : ℕ):
-- imply
  (a ++ b).eraseIdx (a.length + i) = a ++ b.eraseIdx i := by
-- proof
  grind


-- created on 2025-06-09
