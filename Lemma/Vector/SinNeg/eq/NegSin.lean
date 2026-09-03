import Lemma.Real.SinNeg.eq.NegSin
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetSin.eq.SinGet
import sympy.vector.functions
open Real Vector


@[main]
private lemma main
-- given
  (x : List.Vector ℝ n) :
-- imply
  (-x).sin = -x.sin := by
-- proof
  ext i
  rw [GetSin.eq.SinGet.fin, GetNeg.eq.NegGet.fin, SinNeg.eq.NegSin, GetNeg.eq.NegGet.fin, GetSin.eq.SinGet.fin]


-- created on 2026-09-03
