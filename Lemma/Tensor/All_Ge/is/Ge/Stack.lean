import Lemma.Tensor.All_Ge.of.Ge.Stack
import Lemma.Tensor.GeStack.of.All_Ge
open Tensor


@[main]
private lemma main
  [LE α]
  {f g : Fin n → Tensor α s} :
-- imply
  (∀ i : Fin n, f i ≥ g i) ↔ [i < n] f i ≥ [i < n] g i :=
-- proof
  ⟨GeStack.of.All_Ge, All_Ge.of.Ge.Stack⟩


-- created on 2022-03-31
