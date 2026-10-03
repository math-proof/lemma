import Mathlib
import sympy.Basic


/--
[AdicCompletion_isAdicComplete_map_algebraMap_of_fg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_isAdicComplete_map_algebraMap_of_fg.lean)
-/
@[main]
private lemma main
  [CommRing B]
  {I : Ideal B}
-- given
  (hI : I.FG) :
-- imply
  IsAdicComplete (I.map (algebraMap B (AdicCompletion I B))) (AdicCompletion I B) := by
-- proof
  rw [IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hI


-- created on 2026-10-01
