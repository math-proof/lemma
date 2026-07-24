import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.XEq.is.All_XEqGetS
open Tensor


@[main, comm, mp, mpr]
private lemma main
  [XEq α]
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
    apply XEq.is.All_XEqGetS


-- created on 2025-12-24
