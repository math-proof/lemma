/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

/-- The discriminant `1 - 2X - 3X²` in the generating functions for the Motzkin triangle. -/
noncomputable def motzkinDiscriminant : PowerSeries ℚ :=
  PowerSeries.C 1 - PowerSeries.C 2 * PowerSeries.X -
    PowerSeries.C 3 * PowerSeries.X ^ 2

/-- A square root of `motzkinDiscriminant` on the branch with constant coefficient one. -/
def IsMotzkinSquareRoot (s : PowerSeries ℚ) : Prop :=
  s * s = motzkinDiscriminant ∧ PowerSeries.constantCoeff s = 1

/-- The canonical square-root branch used by the Motzkin generating functions. -/
noncomputable def motzkinSquareRoot : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (motzkinDiscriminant - 1)

end MetaMathlibExt
