import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.Head.eq.Get_0
open Vector


@[main]
private lemma main
  {β : Type*}
  {n : ℕ}
-- given
  (v : List.Vector α n.succ)
  (f : α → β) :
-- imply
  (v.map f).head = f v.head := by
-- proof
  simp only [Head.eq.Get_0.fin]
  apply GetMap.eq.UFnGet.fin


-- created on 2026-08-27
