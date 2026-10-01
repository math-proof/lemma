import Lemma.Tensor.LtGetS.of.Lt
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
  [LT α]
  {f g : Fin n → Tensor α s}
-- given
  (h : [i < n] f i < [i < n] g i) :
-- imply
  ∀ i : Fin n, f i < g i := by
-- proof
  intro i
  have := LtGetS.of.Lt h i
  erw [EqGetStack, EqGetStack] at this
  exact this


-- created on 2026-09-27
