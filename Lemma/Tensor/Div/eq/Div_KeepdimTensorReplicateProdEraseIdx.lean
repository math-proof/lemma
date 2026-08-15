import Lemma.Tensor.BFn.eq.BFn_KeepdimTensorReplicateProdEraseIdx
open Tensor


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  X / δ = X / (⟨List.Vector.replicate (s.eraseIdx d).prod δ⟩ : Tensor α (s.eraseIdx d)).keepdim :=
-- proof
  BFn.eq.BFn_KeepdimTensorReplicateProdEraseIdx X δ d


-- created on 2026-08-15
