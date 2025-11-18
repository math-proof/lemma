import sympy.tensor.tensor
import Lemma.Tensor.SelectCast.as.Select.of.Eq
import Lemma.Bool.EqCast.of.SEq
open Tensor Bool


@[main]
private lemma main
-- given
  (h_s : s = s')
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).select ⟨d, by grind⟩ ⟨i, by aesop⟩ = cast (by simp_all) (X.select d i) := by
-- proof
  apply Eq_Cast.of.SEq
  apply SelectCast.as.Select.of.Eq h_s


-- created on 2025-10-05
