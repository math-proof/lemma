import Lemma.Algebra.EqGetRange
import Lemma.Algebra.Add
open Algebra


@[main]
private lemma main
  [Add α]
-- given
  (f g : Fin n → α) :
-- imply
  (List.Vector.range n).map f + (List.Vector.range n).map g = (List.Vector.range n).map (fun i => f i + g i) := by
-- proof
  ext i
  simp [HAdd.hAdd]
  simp [Add.add]
  rw [EqGetRange.fin]
  simp [HAdd.hAdd]


-- created on 2025-07-20
