import Def.Data.Holor.Relu


@[path]
private lemma main
  {x : ℝ} :
-- imply
  x = if 0 ≤ x then relu x else -relu (-x) := by
-- proof
  unfold relu
  if h : 0 ≤ x then
    simp [h]
  else
    have hx : x < 0 := lt_of_not_ge h
    have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_lt hx)
    simp [h, max_eq_left hneg]


-- created on 2021-12-25
-- updated on 2026-10-26
