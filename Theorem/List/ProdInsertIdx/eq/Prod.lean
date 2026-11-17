module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.ProdInsertIdx.eq.Prod
  [MulOneClass α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.insertIdx i 1).prod = s.prod := by
-- proof
  induction s generalizing i <;>
    cases i <;>
      simp_all


-- created on 2025-06-08
