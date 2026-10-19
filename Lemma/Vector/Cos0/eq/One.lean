import Lemma.Real.Cos0.eq.One
import Lemma.Vector.GetCos.eq.CosGet
open Real Vector


@[path]
private lemma main :
-- imply
  (0 : List.Vector ℝ n).cos = 1 := by
-- proof
  ext i
  rw [GetCos.eq.CosGet.fin, EqGet0_0.fin, Cos0.eq.One, EqGet1_1.fin]


-- created on 2026-09-03
