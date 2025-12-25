import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Setoid.is.All_SetoidGetS
open Tensor


@[main, comm, mp, mpr]
private lemma main
  [Setoid α]
-- given
  (h : s.length > 0)
  (A B : Tensor α s) :
-- imply
  A ≈ B ↔ ∀ i : Fin s[0], A.get ⟨i, by apply GtLength.of.GtLength_0 h⟩ ≈ B.get ⟨i, by apply GtLength.of.GtLength_0 h⟩ := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply Setoid.is.All_SetoidGetS


-- created on 2025-12-24
