import Lemma.Tensor.BFn.eq.BFn_KeepdimTensorReplicateProdEraseIdx
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  X * δ = X * (⟨List.Vector.replicate (s.eraseIdx d).prod δ⟩ : Tensor α (s.eraseIdx d)).keepdim :=
-- proof
  BFn.eq.BFn_KeepdimTensorReplicateProdEraseIdx (f := (· * · : α → α → α)) X δ d


-- created on 2025-12-04
-- updated on 2026-08-15
