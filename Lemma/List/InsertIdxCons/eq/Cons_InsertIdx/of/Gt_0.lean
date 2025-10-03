import Lemma.List.InsertIdxCons.eq.Cons_InsertIdx
import Lemma.Algebra.EqAddSub.of.Ge
open Algebra List


@[main]
private lemma main
-- given
  (h : n > 0)
  (v : List α)
  (x v₀ : α) :
-- imply
  (v₀ :: v).insertIdx n x = v₀ :: v.insertIdx (n - 1) x := by
-- proof
  have := InsertIdxCons.eq.Cons_InsertIdx v x v₀ (n - 1)
  rw [EqAddSub.of.Ge (by linarith)] at this
  assumption


-- created on 2025-07-12
