import Lemma.Tensor.All_Le.of.Le.Stack
import Lemma.Tensor.LeStack.of.All_Le
open Tensor


@[main]
private lemma main
  [LE α]
  {f g : Fin n → Tensor α s} :
-- imply
  (∀ i : Fin n, f i ≤ g i) ↔ [i < n] f i ≤ [i < n] g i :=
-- proof
  ⟨LeStack.of.All_Le, All_Le.of.Le.Stack⟩


-- created on 2026-09-27
