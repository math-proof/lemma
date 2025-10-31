import Lemma.List.InsertIdxCons.eq.Cons_InsertIdx
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : n > 0)
  (s : List α)
  (x s₀ : α) :
-- imply
  (s₀ :: s).insertIdx n x = s₀ :: s.insertIdx (n - 1) x := by
-- proof
  have := InsertIdxCons.eq.Cons_InsertIdx s x s₀ (n - 1)
  rwa [EqAddSub.of.Ge (by linarith)] at this


-- created on 2025-07-12
