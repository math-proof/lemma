module

public import Def.Data.List.List.Basic

public section

public theorem List.LengthProduct.eq.ProdMap
-- given
  (s : List (List α)) :
-- imply
  (itertools.product s).length = (s.map List.length).prod := by
-- proof
  unfold itertools.product
  induction s <;>
    simp_all [List.foldr]


-- created on 2025-06-11
-- updated on 2026-10-26
