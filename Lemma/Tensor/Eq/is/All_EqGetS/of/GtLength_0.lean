import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GtLength.of.GtLength_0
import sympy.tensor.tensor
open Tensor


@[main, comm, mp, mpr]
private lemma main
-- given
  (h : s.length > 0)
  (A B : Tensor α s) :
-- imply
  A = B ↔ ∀ i : Fin s[0], A.get ⟨i, by apply GtLength.of.GtLength_0 h⟩ = B.get ⟨i, by apply GtLength.of.GtLength_0 h⟩ := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    apply Eq.is.All_EqGetS


-- created on 2025-11-06
