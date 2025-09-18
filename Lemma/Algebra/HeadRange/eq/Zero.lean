import stdlib.List.Vector
import Lemma.Algebra.Head.eq.Get_0
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  (List.Vector.range n.succ).head = 0 := by
-- proof
  rw [Head.eq.Get_0]
  simp [List.Vector.get]
  simp [List.Vector.range]


-- created on 2025-07-11
