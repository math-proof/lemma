import Lemma.Vector.ValGetUnflatten.eq.ValArraySlice
import Lemma.Vector.EqUnflattenFlatten
import Lemma.Vector.GetUnflatten.as.ArraySlice
import Lemma.List.Prod.eq.Foldr
import Lemma.Tensor.GetUnflattenDataStack.eq.Data
import Lemma.Bool.SEq.is.Eq
open Tensor Vector List Bool


@[main]
private lemma fin
-- given
  (f : Fin n → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).data.array_slice (i * s.prod) s.prod ≃ (f i).data := by
-- proof
  have := ArraySlice.as.GetUnflatten ([i < n] f i).data i
  simp at this
  apply SEq.trans this
  apply SEq.of.Eq
  apply GetUnflattenDataStack.eq.Data.fin


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).data.array_slice (i * s.prod) s.prod ≃ (f i).data := by
-- proof
  apply fin _ i


-- created on 2025-05-23
-- updated on 2025-07-17
