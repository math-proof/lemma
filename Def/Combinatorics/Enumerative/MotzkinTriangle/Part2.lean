/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.MotzkinTriangle
/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

/-- The second component of the canonical Motzkin Riordan pair. It is the
power-series quotient `(1 - X - motzkinSquareRoot) / (2X)`, expressed by a
coefficient shift so no division by `X` is required. -/
noncomputable def motzkinH : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1) (1 - PowerSeries.X - motzkinSquareRoot) / 2

end MetaMathlibExt
