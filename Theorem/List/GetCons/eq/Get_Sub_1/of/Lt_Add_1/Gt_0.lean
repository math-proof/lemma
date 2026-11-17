module

public import Def.Data.List.List.Basic

public section

public theorem List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
  {tail : List α}
-- given
  (h₂ : i > 0)
  (h₀ : i < tail.length + 1)
  (head : α) :
-- imply
  (head :: tail)[i] = tail[i - 1] := by
-- proof
  grind


-- created on 2025-05-15
