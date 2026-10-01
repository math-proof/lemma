import Lemma.Tensor.LeGetS.of.Le
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
  [LE α]
  {f g : Fin n → Tensor α s}
-- given
  (h : [i < n] f i ≥ [i < n] g i) :
-- imply
  ∀ i : Fin n, f i ≥ g i := by
-- proof
  intro i
  have := LeGetS.of.Le h i
  erw [EqGetStack, EqGetStack] at this
  exact this


-- created on 2022-03-31
