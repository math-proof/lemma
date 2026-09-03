import Lemma.Real.Cos0.eq.One
import Lemma.Vector.EqGet0_0
import Lemma.Vector.EqGet1_1
import Lemma.Vector.GetCos.eq.CosGet
import sympy.vector.functions
open Real Vector


@[main]
private lemma main :
-- imply
  (0 : List.Vector ℝ n).cos = 1 := by
-- proof
  ext i
  rw [GetCos.eq.CosGet.fin, EqGet0_0.fin, Cos0.eq.One, EqGet1_1.fin]


-- created on 2026-09-03
