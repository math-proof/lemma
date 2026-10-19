import Lemma.Real.Sin0.eq.Zero
import Lemma.Vector.GetSin.eq.SinGet
open Real Vector


@[path]
private lemma main :
-- imply
  (0 : List.Vector ℝ n).sin = 0 := by
-- proof
  ext i
  rw [GetSin.eq.SinGet.fin, EqGet0_0.fin, Sin0.eq.Zero]


-- created on 2026-09-03
