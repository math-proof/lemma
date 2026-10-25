/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.MotzkinTriangle.Part3
/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

/-- The pair of generating series defining the Motzkin Riordan array.

Writing the second identity without division by `X` keeps the characterization internal to formal
power series. The constant-coefficient condition selects the intended square-root branch. -/
def IsMotzkinRiordanPair (g h : PowerSeries ℚ) : Prop :=
  ∃ s : PowerSeries ℚ,
    IsMotzkinSquareRoot s ∧ g * s = 1 ∧
      2 * PowerSeries.X * h = 1 - PowerSeries.X - s

end MetaMathlibExt
