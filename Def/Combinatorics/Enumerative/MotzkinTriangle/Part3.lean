/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.MotzkinTriangle.Part2

@[expose] public section

/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

/-- The first component of the canonical Motzkin Riordan pair. -/
noncomputable def motzkinG : PowerSeries ℚ :=
  motzkinSquareRoot⁻¹

end MetaMathlibExt
