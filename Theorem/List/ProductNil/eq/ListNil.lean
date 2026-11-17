module

public import Def.Data.List.List.Basic

public section

public theorem List.ProductNil.eq.ListNil:
-- imply
  itertools.product ([] : List (List α)) = [[]] := by
-- proof
  unfold itertools.product
  simp


-- created on 2025-06-14
