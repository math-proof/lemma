/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.MotzkinTriangle.Part3

@[expose] public section

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
