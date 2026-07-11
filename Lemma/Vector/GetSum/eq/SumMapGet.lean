import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.SumCons.eq.Add_Sum
open Vector Finset


@[main, fin, val]
private lemma main
  [Add α] [Zero α]
-- given
  (x : List.Vector (List.Vector α n) m)
  (i : Fin n) :
-- imply
  x.sum[i] = (x.map (·[i])).sum := by
-- proof
  induction x using List.Vector.inductionOn with
  | nil =>
    simp [List.Vector.sum]
    apply EqGet0_0
  | cons ih =>
    rw [SumCons.eq.Add_Sum, GetAdd.eq.AddGetS, ih]
    congr 1


-- created on 2025-10-11
-- updated on 2026-07-11
