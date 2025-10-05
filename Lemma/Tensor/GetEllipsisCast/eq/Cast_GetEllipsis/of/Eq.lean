import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.GetEllipsisCast.as.GetEllipsis.of.Eq
import Lemma.Logic.EqCast.of.SEq
open Tensor Logic


@[main]
private lemma main
  {s s' : List ℕ}
-- given
  (h_s : s' = s)
  (X : Tensor α s)
  (dim : Fin s.length)
  (i : Fin s[dim]) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h_s]
  (cast h X).getEllipsis ⟨dim, by simp_all⟩ ⟨i, by simp_all⟩ = cast (by simp_all) (X.getEllipsis dim i) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetEllipsisCast.as.GetEllipsis.of.Eq h_s


-- created on 2025-10-05
