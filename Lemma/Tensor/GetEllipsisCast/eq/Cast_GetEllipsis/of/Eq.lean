import sympy.tensor.tensor
import Lemma.Tensor.GetEllipsisCast.as.GetEllipsis.of.Eq
import Lemma.Bool.EqCast.of.SEq
open Tensor Bool


@[main]
private lemma main
-- given
  (h_s : s = s')
  (X : Tensor α s)
  (dim : Fin s.length)
  (i : Fin s[dim]) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).getEllipsis ⟨dim, by grind⟩ ⟨i, by aesop⟩ = cast (by simp_all) (X.getEllipsis dim i) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetEllipsisCast.as.GetEllipsis.of.Eq h_s


-- created on 2025-10-05
