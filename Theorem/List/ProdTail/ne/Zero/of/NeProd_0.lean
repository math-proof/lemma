module
public import Theorem.List.ProdDrop.ne.Zero.of.NeProd_0
public import Lemma.List.Tail.eq.Drop_1
open List


public section

@[path]
private theorem main
  [MonoidWithZero α]
  {s : List α}
-- given
  (h : s.prod ≠ 0) :
-- imply
  s.tail.prod ≠ 0 := by
-- proof
  rw [Tail.eq.Drop_1]
  apply ProdDrop.ne.Zero.of.NeProd_0 h


-- created on 2025-12-02
