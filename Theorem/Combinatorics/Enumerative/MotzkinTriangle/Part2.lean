/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MotzkinTriangle.Part2
/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

theorem two_mul_X_mul_motzkinH :
    2 * PowerSeries.X * motzkinH = 1 - PowerSeries.X - motzkinSquareRoot := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm, mul_assoc]
  ext n
  cases n with
  | zero =>
      simp [motzkinSquareRoot_isSquareRoot.2]
  | succ n =>
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      simp [motzkinH]
      ring

end MetaMathlibExt
