import Lemma.Real.Sin0.eq.Zero
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetSin.eq.SinGet
import sympy.vector.functions
open Real Vector


@[main]
private lemma main :
-- imply
  (0 : List.Vector ℝ n).sin = 0 := by
-- proof
  ext i
  rw [GetSin.eq.SinGet.fin, EqGet0_0.fin, Sin0.eq.Zero]


-- created on 2026-09-03
