import Def.Data.List.List.Part5


@[path]
private lemma main:
-- imply
  itertools.product ([] : List (List α)) = [[]] := by
-- proof
  unfold itertools.product
  simp


-- created on 2025-06-14
