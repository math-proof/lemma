import Lemma.Tensor.EqGet0_0
import sympy.matrices.dense
open Tensor


@[main]
private lemma main
  [Zero α]
  {m n : ℕ} :
-- imply
  (0 : Tensor α [m, n]).toMatrix = 0 := by
-- proof
  ext i j
  have hz := EqGet0_0.fin (α := α) (s := [m, n]) ⟨(i : ℕ), i.isLt⟩
  have hz' := EqGet0_0.fin (α := α) (s := [n]) ⟨(j : ℕ), j.isLt⟩
  simp [Tensor.toMatrix, GetElem.getElem] at hz hz' ⊢
  rw [hz]
  exact hz'


-- created on 2026-09-07
