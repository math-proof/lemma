import Lemma.Tensor.LeStackS.of.All_Le
open Tensor


@[main]
private lemma main
  [LE α]
  {f g : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, f i ≥ g i) :
-- imply
  [i < n] f i ≥ [i < n] g i :=
-- proof
  LeStackS.of.All_Le h


-- created on 2022-01-01
