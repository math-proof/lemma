import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  ⌊x⌋ ∈ Set.Ico ⌊a⌋ ⌈b⌉ := by
-- proof
  constructor
  · apply Int.floor_le_floor h.1
  · apply Int.lt_ceil.mpr
    apply lt_of_le_of_lt (Int.floor_le x) h.2


-- created on 2021-03-05
-- updated on 2023-04-17
