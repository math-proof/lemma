import Lemma.Real.CosNeg.eq.Cos
import Lemma.Vector.GetCos.eq.CosGet
import Lemma.Vector.GetNeg.eq.NegGet
import sympy.vector.functions
open Real Vector


@[main]
private lemma main
-- given
  (x : List.Vector ℝ n) :
-- imply
  (-x).cos = x.cos := by
-- proof
  ext i
  rw [GetCos.eq.CosGet.fin, GetNeg.eq.NegGet.fin, CosNeg.eq.Cos, GetCos.eq.CosGet.fin]


-- created on 2026-09-03
