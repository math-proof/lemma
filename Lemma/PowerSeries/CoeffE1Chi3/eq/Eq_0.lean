import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularForm_EisensteinChiNegThree
open EisensteinWeightOne


/--
[EisensteinWeightOne_coeff_e1Chi3](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_EisensteinWeightOne_coeff_e1Chi3.lean)
-/
@[path]
private lemma main
  {n : ℕ} :
-- imply
  PowerSeries.coeff n e1Chi3 = if n = 0 then 1 else 6 * sigmaChi n := by
-- proof
  rw [e1Chi3, PowerSeries.coeff_mk]


-- created on 2026-10-23
