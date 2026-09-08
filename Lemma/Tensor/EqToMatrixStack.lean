import Lemma.Tensor.EqGetStack
import sympy.matrices.dense
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
-- given
  (f : Fin m → Fin n → Tensor α []) :
-- imply
  ([i < m] [j < n] f i j).toMatrix = f := by
-- proof
  ext i j
  simp only [Tensor.toMatrix]
  have hrow := EqGetStack.fin (fun i : Fin m => [j < n] f i j) i
  have hcol := EqGetStack.fin (fun j : Fin n => f i j) j
  simp [GetElem.getElem] at hrow hcol ⊢
  erw [hrow, hcol]


-- created on 2019-10-16
-- updated on 2026-09-08
