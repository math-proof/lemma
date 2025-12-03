import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
open Tensor


@[main]
private lemma main
  [Mul α]
  {s : List ℕ}
-- given
  (a b : List.Vector α s.prod) :
-- imply
  (⟨a * b⟩ : Tensor α s) = (⟨a⟩ : Tensor α s) * (⟨b⟩ : Tensor α s) := by
-- proof
  apply Eq.of.EqDataS
  simp [DataMul.eq.MulDataS]


-- created on 2025-12-03
