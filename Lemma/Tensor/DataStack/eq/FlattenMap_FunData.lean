import Lemma.Tensor.GetUnflattenDataStack.eq.Data
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqGetRange
import Lemma.Vector.EqUnflatten.is.Eq_Flatten
import sympy.tensor.stack
open Tensor Vector


@[main]
private lemma fin
-- given
  (f : Fin n → Tensor α s) :
-- imply
  ([i < n] f i).data = ((List.Vector.range n).map fun i => (f i).data).flatten := by
-- proof
  apply Eq_Flatten.of.EqUnflatten
  apply Eq.of.All_EqGetS
  intro i
  rw [GetUnflattenDataStack.eq.Data.fin]
  simp [EqGetRange.val i]


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s) :
-- imply
  ([i < n] f i).data = ((List.Vector.range n).map fun i => (f i.val).data).flatten := by
-- proof
  apply fin


-- created on 2025-11-14
