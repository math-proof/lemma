import Lemma.Real.AddArcsinS.eq.DivPi2.of.Ge_0
import Lemma.Real.Arccos.eq.Sub_Arcsin
import Lemma.Real.SubArcsinS.eq.DivPi2.of.Lt_0
open Real


@[main]
private lemma main
  {x : ℝ} :
-- imply
  arccos x = if 0 ≤ x then
    arcsin (√(1 - x²))
  else
    π - arcsin (√(1 - x²)) := by
-- proof
  rw [Arccos.eq.Sub_Arcsin]
  if h : 0 ≤ x then
    simp [h]
    linarith [AddArcsinS.eq.DivPi2.of.Ge_0 h]
  else
    simp [h]
    linarith [SubArcsinS.eq.DivPi2.of.Lt_0 (lt_of_not_ge h)]


-- created on 2018-07-14
-- updated on 2026-08-06
