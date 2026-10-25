import Mathlib
import sympy.Basic
import Lemma.WeierstrassCurve.VeluQuotientOfSums
import Lemma.Int.P2MUtil
open WeierstrassCurve Int


/--
[WeierstrassCurve_map_veluQuotientOfSums](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_map_veluQuotientOfSums.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing R']
  {W : WeierstrassCurve R}
  {f : R →+* R'}
  {t w : R} :
-- imply
  (W.veluQuotientOfSums t w).map f = (W.map f).veluQuotientOfSums (f t) (f w) := by
-- proof
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · exact W.map_a₁ f
  · exact W.map_a₂ f
  · exact W.map_a₃ f
  · simp only [veluQuotientOfSums_a₄, map_a₄, map_sub, map_mul, map_ofNat]
  · simp only [veluQuotientOfSums_a₆, map_a₆, map_b₂, map_sub, map_mul, map_ofNat]


-- created on 2026-10-24
