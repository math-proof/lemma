import stdlib.List
import Lemma.List.Permute.eq.Ite
import Lemma.List.Slice.eq.Nil
open List


@[main]
private lemma main
  {a : List α}
-- given
  (i : Fin a.length) :
-- imply
  a.permute i 0 = a := by
-- proof
  rw [Permute.eq.Ite]
  simp
  rw [Slice.eq.Nil]
  simp


-- created on 2025-06-16
