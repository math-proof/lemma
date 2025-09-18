import Lemma.Algebra.ValGetUnflatten.eq.ValArraySlice
import Lemma.Algebra.EqUnflattenFlatten
import Lemma.Algebra.GetUnflatten.as.ArraySlice
import Lemma.Algebra.Prod.eq.Foldr
import Lemma.Tensor.GetUnflattenDataStack.eq.Data
import Lemma.Logic.SEq.of.Eq
open Algebra Tensor Logic


@[main]
private lemma fin
-- given
  (f : Fin n → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).data.array_slice (i * s.prod) s.prod ≃ (f i).data := by
-- proof
  have := ArraySlice.as.GetUnflatten ([i < n] f i).data i
  simp [Foldr.eq.Prod] at this
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
  apply fin


-- created on 2025-05-23
-- updated on 2025-07-17
